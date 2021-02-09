namespace Myriad.Plugins

open System
open Myriad.Core
open FsAst
open Fantomas
open Microsoft.OpenApi.Models
open Microsoft.OpenApi.Readers
open FSharp.Compiler.XmlDoc
open FSharp.Compiler.SyntaxTree
open FSharp.Compiler.Range

[<AutoOpen>]
module private Helpers =
    open System.IO

    let openDefinition (fileName: string) =
        use stream = File.OpenRead(fileName)

        let reader =
            OpenApiStreamReader
                (OpenApiReaderSettings(ReferenceResolution = ReferenceResolutionSetting.ResolveLocalReferences))

        let mutable diag = OpenApiDiagnostic()
        reader.Read(stream, &diag)

    let r = range0

    let createOpen namespaceId =
        let ident =
            LongIdentWithDots.Create
                (Ident.CreateLong namespaceId
                 |> List.map (fun ident -> ident.idText))

        let openTarget =
            SynOpenDeclTarget.ModuleOrNamespace(ident.Lid, r)

        SynModuleDecl.CreateOpen openTarget

    let createModule moduleName (xmlDoc: string option) attrs members =
        let moduleIdent = Ident.CreateLong moduleName

        let moduleInfo =
            { SynComponentInfoRcd.Create moduleIdent with
                  Attributes = attrs
                  XmlDoc = PreXmlDoc.Create xmlDoc }

        SynModuleDecl.CreateNestedModule(moduleInfo, members)

    let createRequireQualifiedAccessAttribute () =
        let attrs =
            SynAttributeList.Create(SynAttribute.RequireQualifiedAccess())

        SynAttributes.Cons(attrs, SynAttributes.Empty)

    let createXmlDoc text =
        if not (String.IsNullOrWhiteSpace text) then Some $" {text}" else None

    let toIdentifier (name: string) =
        let capitalize =
            Seq.mapi (fun i c ->
                match i with
                | 0 -> Char.ToUpper(c)
                | _ -> c)
            >> String.Concat

        name.Split('-', '_')
        |> Seq.map capitalize
        |> String.Concat

    type FsIdentifier = private FsIdentifier of string

    module FsIdentifier =
        let ofString = toIdentifier >> FsIdentifier
        let toString (FsIdentifier ident) = ident
        let toIdent (FsIdentifier ident) = Ident.Create ident
        let toIdentLong (FsIdentifier ident) = Ident.CreateLong ident
        let toSynType (FsIdentifier ident) = SynType.Create ident

    type TypeDef =
        | Record of typeName: FsIdentifier * fields: RecordFieldDef list * xmlDoc: string option
        | AnonymousRecord of fields: RecordFieldDef list
        | Union of FsIdentifier * cases: UnionCaseDef list * xmlDoc: string option
        | Array of TypeDef
        | Tuple of TypeDef list
        | Reference of string
        | Unit

    and RecordFieldDef =
        { Name: FsIdentifier
          Type: TypeDef
          XmlDoc: string option }

    and UnionCaseDef =
        { Name: FsIdentifier
          Fields: UnionCaseFieldDef list
          XmlDoc: string option }

    and UnionCaseFieldDef =
        { Name: FsIdentifier option
          Type: TypeDef }

    module TypeDef =
        let createRecord name fields =
            TypeDef.Record(FsIdentifier.ofString name, fields, None)

        let createRecordWithDoc name fields xmlDoc =
            TypeDef.Record(FsIdentifier.ofString name, fields, Some xmlDoc)

        let createUnion name fields =
            TypeDef.Union(FsIdentifier.ofString name, fields, None)

        let createUnionWithDoc name fields xmlDoc =
            TypeDef.Union(FsIdentifier.ofString name, fields, Some xmlDoc)

        let rec toSynType typeDef =
            match typeDef with
            | TypeDef.AnonymousRecord fields ->
                SynType.AnonRecd
                    (isStruct = false,
                     fields = List.map (fun (f: RecordFieldDef) -> FsIdentifier.toIdent f.Name, toSynType f.Type) fields,
                     range = range.Zero)
            | TypeDef.Record (typeName, _, _)
            | TypeDef.Union (typeName, _, _) -> FsIdentifier.toSynType typeName
            | TypeDef.Array typeDef -> SynType.Array(0, toSynType typeDef, range.Zero)
            | TypeDef.Tuple typeDefs ->
                SynType.Tuple
                    (isStruct = false,
                     elementTypes = List.map (fun t -> false, toSynType t) typeDefs,
                     range = range.Zero)
            | TypeDef.Reference ident -> SynType.Create ident
            | TypeDef.Unit -> SynType.CreateUnit

        let private recordToSynModuleDecl typeName fields xmlDoc =
            let createField (field: RecordFieldDef) =
                { SynFieldRcd.Create(FsIdentifier.toIdent field.Name, toSynType field.Type) with
                      XmlDoc = PreXmlDoc.Create(Option.bind createXmlDoc field.XmlDoc) }

            let requireQualifiedAccessAttr = createRequireQualifiedAccessAttribute ()

            let info =
                { SynComponentInfoRcd.Create(FsIdentifier.toIdentLong typeName) with
                      Attributes = requireQualifiedAccessAttr
                      XmlDoc = PreXmlDoc.Create(Option.bind createXmlDoc xmlDoc) }

            SynTypeDefnRcd.CreateSimple
                (info,
                 SynTypeDefnSimpleReprRcd
                     .Record(SynTypeDefnSimpleReprRecordRcd.Create(List.map createField fields))
                     .FromRcd)

        let private unionToSynModuleDecl typeName cases xmlDoc =
            let requireQualifiedAccessAttr = createRequireQualifiedAccessAttribute ()

            let info =
                { SynComponentInfoRcd.Create(FsIdentifier.toIdentLong typeName) with
                      Attributes = requireQualifiedAccessAttr
                      XmlDoc = PreXmlDoc.Create(Option.bind createXmlDoc xmlDoc) }

            let createCase (case: UnionCaseDef) =
                let createField (field: UnionCaseFieldDef) =
                    let name =
                        field.Name
                        |> Option.map FsIdentifier.toIdent
                        |> Option.defaultValue (Ident.Create "value")

                    SynFieldRcd.Create(name, toSynType field.Type)

                SynUnionCaseRcd.Create
                    (FsIdentifier.toIdent case.Name, SynUnionCaseType.Create(List.map createField case.Fields))

            let union =
                SynTypeDefnSimpleReprRcd.Union(SynTypeDefnSimpleReprUnionRcd.Create(List.map createCase cases))

            SynTypeDefnRcd.CreateSimple(info, union.FromRcd)

        let toSynTypeDef (typeDef: TypeDef) =
            match typeDef with
            | TypeDef.Record (typeName, fields, xmlDoc) ->
                Some
                    (recordToSynModuleDecl typeName fields xmlDoc)
                        .FromRcd
            | TypeDef.AnonymousRecord _ -> None // invalidOp "cannot create SynModuleDecl for Anonymous record"
            | TypeDef.Union (typeName, cases, xmlDoc) ->
                Some
                    (unionToSynModuleDecl typeName cases xmlDoc)
                        .FromRcd
            | TypeDef.Array _ -> None // invalidOp "cannot create SynModuleDecl for Array"
            | TypeDef.Tuple _ -> None // failwith "not implemented yet"
            | TypeDef.Reference id -> None // invalidOp $"cannot create SynModuleDecl for Reference {id}"
            | TypeDef.Unit -> None

    module RecordFieldDef =
        let createWithDoc fieldName type' xmlDoc: RecordFieldDef =
            { Name = FsIdentifier.ofString fieldName
              Type = type'
              XmlDoc = Some xmlDoc }

        let create fieldName type' =
            { Name = FsIdentifier.ofString fieldName
              Type = type'
              XmlDoc = None }

    module UnionCaseFieldDef =
        let create fieldName type': UnionCaseFieldDef =
            { Name = Option.map FsIdentifier.ofString fieldName
              Type = type' }

    module UnionCaseDef =
        let createWithDoc name fields xmlDoc: UnionCaseDef =
            { Name = FsIdentifier.ofString name
              Fields = fields
              XmlDoc = Some xmlDoc }

        let create name fields: UnionCaseDef =
            { Name = FsIdentifier.ofString name
              Fields = fields
              XmlDoc = None }

    [<RequireQualifiedAccess>]
    module rec Schema =
        [<AutoOpen>]
        module Types =
            let (|Reference|_|) (schema: OpenApiSchema) =
                Option.ofObj schema.Reference
                |> Option.filter (fun r -> r.IsLocal || r.IsExternal)

            let (|String|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "string", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|Enum|_|) (schema: OpenApiSchema) = Option.ofObj schema.Enum

            let (|Date|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "string", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "date", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|DateTime|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "string", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "date-time", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|Byte|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "string", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "byte", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|Binary|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "string", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "binary", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|Double|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "number", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "double", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|Float|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "number", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|Int32|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "integer", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|Int64|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "integer", StringComparison.OrdinalIgnoreCase)
                   && String.Equals(schema.Format, "int64", StringComparison.OrdinalIgnoreCase) then
                    Some schema
                else
                    None

            let (|Boolean|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "boolean", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|Array|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "array", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|Object|_|) (schema: OpenApiSchema) =
                if String.Equals(schema.Type, "object", StringComparison.OrdinalIgnoreCase)
                then Some schema
                else None

            let (|OneOf|_|) (schema: OpenApiSchema) =
                Option.ofObj schema.OneOf
                |> Option.filter (Seq.isEmpty >> not)

            let (|AnyOf|_|) (schema: OpenApiSchema) =
                Option.ofObj schema.AnyOf
                |> Option.filter (Seq.isEmpty >> not)

            let (|AllOf|_|) (schema: OpenApiSchema) =
                Option.ofObj schema.AllOf
                |> Option.filter (Seq.isEmpty >> not)

            let (|Not|_|) (schema: OpenApiSchema) = Option.ofObj schema.Not

        let private mapToTypeDef (schema: OpenApiSchema) (nameHint: string option) =
            match schema with
            | OneOf ls -> createOneOfDef schema (List.ofSeq ls) nameHint
            | AnyOf ls -> TypeDef.Unit, []
            | AllOf ls -> createAllOfDef (List.ofSeq ls)
            | Date _ -> handlePrimitiveType (TypeDef.Reference "NodaTime.OffsetDateTime") schema
            | DateTime _ -> handlePrimitiveType (TypeDef.Reference "NodaTime.LocalDate") schema
            | Byte _ -> handlePrimitiveType (TypeDef.Reference "byte[]") schema
            | Binary _ -> handlePrimitiveType (TypeDef.Reference "System.IO.Stream") schema
            | String _ -> handlePrimitiveType (TypeDef.Reference "string") schema
            | Double _ -> handlePrimitiveType (TypeDef.Reference "double") schema
            | Float _ -> handlePrimitiveType (TypeDef.Reference "float") schema
            | Int64 _ -> handlePrimitiveType (TypeDef.Reference "int64") schema
            | Int32 _ -> handlePrimitiveType (TypeDef.Reference "int") schema
            | Boolean _ -> handlePrimitiveType (TypeDef.Reference "bool") schema
            | Array s -> createArrayDef s nameHint
            | Object s -> createObjectDef s
            | _ -> invalidOp $"{schema.Reference.Id}, {schema.Type}, {schema.Format} not supported"

        let private createObjectDef (schema: OpenApiSchema) =
            let prop n s =
                let typ, subTypes = mapToTypeDef s (Some n)
                RecordFieldDef.create n typ, subTypes

            let fields, subTypes =
                schema.Properties
                |> Seq.map (fun kv -> prop kv.Key kv.Value)
                |> Seq.toList
                |> List.unzip

            let recordDef =
                match Option.ofObj schema.Reference with
                | Some r -> TypeDef.createRecord r.Id fields
                | None -> TypeDef.AnonymousRecord fields

            recordDef, List.collect id subTypes

        let private createArrayDef (schema: OpenApiSchema) nameHint =
            let itemType, subTypes =
                mapToTypeDef schema.Items (Option.map (fun n -> $"{n}Item") nameHint)

            TypeDef.Array itemType, subTypes

        let private createOneOfDef (schema: OpenApiSchema) (schemas: OpenApiSchema list) nameHint =
            let create name schemas =
                let duCases, subTypes =
                    let fieldCount = List.length schemas

                    let duCase fieldCount fieldIdx s =
                        let typ, subTypes = mapToTypeDef s None
                        let ident = FsIdentifier.ofString name

                        UnionCaseDef.create
                            $"%s{FsIdentifier.toString ident}%i{fieldIdx}Of%i{fieldCount}"
                            [ UnionCaseFieldDef.create None typ ],
                        subTypes

                    schemas
                    |> List.mapi (duCase fieldCount)
                    |> List.unzip

                let union = TypeDef.createUnion name duCases
                union, List.collect id subTypes

            match Option.ofObj schema.Reference, nameHint with
            | None, None -> failwith "Anonymous union type not implemented yet (oneOf)"
            | None, Some name -> create name schemas
            | Some r, _ -> create r.Id schemas

        let private createAllOfDef (schemas: OpenApiSchema list) =
            let tupleItems, subTypes =
                schemas
                |> List.map (fun s -> mapToTypeDef s None)
                |> List.unzip

            TypeDef.Tuple tupleItems, List.collect id subTypes

        let private handlePrimitiveType typeRef (schema: OpenApiSchema) =
            match Option.ofObj schema.Reference with
            | Some r ->
                let duCase =
                    UnionCaseDef.create r.Id [ UnionCaseFieldDef.create None typeRef ]

                TypeDef.createUnionWithDoc r.Id [ duCase ] schema.Description, []
            | None -> typeRef, []

        let createTypeDefs (schema: OpenApiSchema) nameHint = mapToTypeDef schema (Some nameHint)

    [<RequireQualifiedAccess>]
    module Operations =
        [<Literal>]
        let HandlerTypeName = "IHandler"

        [<Literal>]
        let HandleMethodName = "Handle"

        let private createRequestTypes (operation: OpenApiOperation) =
            let requestBody =
                match Option.ofObj operation.RequestBody with
                | Some r ->
                    if r.Content.Count <> 1
                    then invalidOp "Content-Negotiated request body not supported"

                    let type', subTypes =
                        Schema.createTypeDefs (Seq.head r.Content).Value.Schema "RequestBody"

                    Some(RecordFieldDef.create "RequestBody" type', type' :: subTypes)
                | None -> None

            let parameters (location: ParameterLocation) =
                //                operation.Parameters.[0].In
                None

            let fields, types =
                [ requestBody
                  parameters ParameterLocation.Path
                  parameters ParameterLocation.Query
                  parameters ParameterLocation.Header
                  parameters ParameterLocation.Cookie ]
                |> List.choose id
                |> List.unzip

            if List.isEmpty fields
            then TypeDef.Unit, []
            else TypeDef.createRecordWithDoc "Request" fields operation.Description, List.collect id types

        let private createResponseType (opResponses: OpenApiResponses) =
            let duCases, types =
                let duCase status (response: OpenApiResponse) =
                    let ident =
                        if String.Equals("default", status) then "Default" else $"Http{status}"

                    let duCaseField, subTypes =
                        match Seq.toList response.Content with
                        | [] -> [], []
                        | [ kv ] ->
                            let type', subTypes =
                                Schema.createTypeDefs kv.Value.Schema ident

                            [ UnionCaseFieldDef.create None type' ], subTypes
                        | _ -> invalidOp "Content-Negotiated response body not supported"

                    UnionCaseDef.createWithDoc ident duCaseField response.Description, subTypes

                opResponses
                |> Seq.map (fun r -> duCase r.Key r.Value)
                |> Seq.toList
                |> List.unzip

            TypeDef.createUnion "Response" duCases, List.collect id types

        let private createHandlerType requestType responseType =
            let typeIdent = Ident.CreateLong HandlerTypeName

            let handleValField =
                let ident = Ident.Create HandleMethodName

                let funcDecl =
                    SynType.CreateFun(TypeDef.toSynType requestType, TypeDef.toSynType responseType)

                let fieldRcd =
                    SynFieldRcd.Create(ident, funcDecl, false)

                SynMemberDefn.ValField(fieldRcd.FromRcd, range.Zero)

            let info = SynComponentInfoRcd.Create typeIdent
            SynModuleDecl.CreateType(info, SynMemberDefns.Cons(handleValField, SynMemberDefns.Empty))

        let private createHandleMethod path (method: OperationType) requestType responseType =
            let handlerParamName = "handler"

            let handlerParam =
                SynPatRcd.CreateTyped
                    (SynPatRcd.CreateNamed(Ident.Create handlerParamName, SynPatRcd.CreateWild),
                     SynType.HashConstraint(SynType.Create HandlerTypeName, range.Zero))
                |> SynPatRcd.CreateParen

            let requestParam =
                match requestType with
                | TypeDef.Unit -> None
                | t ->
                    let name = "request"

                    let patRcd =
                        SynPatRcd.CreateTyped
                            (SynPatRcd.CreateNamed(Ident.Create name, SynPatRcd.CreateWild),
                             TypeDef.toSynType requestType)

                    Some(name, SynPatRcd.CreateParen patRcd)

            let pattern =
                let name = LongIdentWithDots.CreateString "handle"

                let handleParams =
                    [ yield handlerParam
                      match requestParam with
                      | Some (_, p) -> yield p
                      | None -> () ]

                SynPatRcd.CreateLongIdent(name, handleParams)

            let expr =
                let matchExpr =
                    let instAndMethod =
                        LongIdentWithDots.CreateString $"{handlerParamName}.{HandleMethodName}"

                    let paramsExpr =
                        match requestParam with
                        | None -> SynExpr.CreateUnit
                        | Some (n, p) -> SynExpr.CreateIdent(Ident.Create n)

                    SynExpr.CreateInstanceMethodCall(instAndMethod, paramsExpr)

                let clauses =
                    let clause typeName (case: UnionCaseDef) =
                        let fn =
                            SynExpr.CreateInstanceMethodCall
                                (LongIdentWithDots.CreateString "text",
                                 SynExpr.CreateConst
                                     (SynConst.CreateString
                                         $"%O{method} on %s{path} returned %s{FsIdentifier.toString case.Name}"))

                        let args =
                            case.Fields
                            |> List.map (fun f ->
                                SynPatRcd.CreateNamed
                                    (f.Name
                                     |> Option.map FsIdentifier.toIdent
                                     |> Option.defaultValue (Ident.Create "value"),
                                     SynPatRcd.CreateWild))

                        let patRcd =
                            SynPatRcd.CreateLongIdent
                                (LongIdentWithDots.Create [ FsIdentifier.toString typeName
                                                            FsIdentifier.toString case.Name ],
                                 args)

                        SynMatchClause.Clause(patRcd.FromRcd, None, fn, range.Zero, DebugPointForTarget.No)

                    match responseType with
                    | TypeDef.Union (name, cases, _) -> List.map (clause name) cases
                    | _ -> invalidArg (nameof responseType) "Expected to be a Union"

                SynExpr.CreateMatch(matchExpr, clauses)

            SynModuleDecl.CreateLet [ { SynBindingRcd.Let with
                                            Pattern = pattern
                                            Expr = expr } ]

        let createModule path (method: OperationType) (operation: OpenApiOperation) =
            let requireQualifiedAccessAttr = createRequireQualifiedAccessAttribute ()
            let requestType, requestSubTypes = createRequestTypes operation

            let requestTypeDefs =
                match requestType with
                | TypeDef.Unit -> requestSubTypes
                | _ -> requestType :: requestSubTypes
                |> List.choose TypeDef.toSynTypeDef

            let responseType, responseSubTypes = createResponseType operation.Responses

            let responseTypeDefs =
                match responseType with
                | TypeDef.Unit -> responseSubTypes
                | _ -> responseType :: responseSubTypes
                |> List.choose TypeDef.toSynTypeDef

            let models =
                SynModuleDecl.Types(requestTypeDefs @ responseTypeDefs, range.Zero)

            createModule
                operation.OperationId
                (createXmlDoc operation.Description)
                requireQualifiedAccessAttr
                (createOpen "Models"
                 :: models
                    :: [ createHandlerType requestType responseType
                         createHandleMethod path method requestType responseType ])


[<MyriadGenerator("openapi-giraffe")>]
type OpenApiGiraffeGenerator() =
    interface IMyriadGenerator with
        member _.ValidInputExtensions =
            seq {
                ".yaml"
                ".yml"
                ".json"
            }

        member _.Generate(context: GeneratorContext) =
            let definition = openDefinition context.InputFileName

            let modelTypes =
                definition.Components.Schemas
                |> Seq.collect (fun sc ->
                    let type', subTypes = Schema.createTypeDefs sc.Value sc.Key
                    type' :: subTypes)
                |> Seq.choose TypeDef.toSynTypeDef
                |> Seq.toList

            let operationModules =
                definition.Paths
                |> Seq.collect (fun ps ->
                    ps.Value.Operations
                    |> Seq.map (fun ops -> Operations.createModule ps.Key ops.Key ops.Value))
                |> Seq.toList

            List.singleton
                { SynModuleOrNamespaceRcd.CreateModule(Ident.CreateLong "Server") with
                      IsRecursive = false
                      Declarations =
                          [ createOpen "Giraffe"
                            createModule "Models" None SynAttributes.Empty [ SynModuleDecl.Types(modelTypes, range0) ]
                            createModule "Operations" None SynAttributes.Empty operationModules ] }
