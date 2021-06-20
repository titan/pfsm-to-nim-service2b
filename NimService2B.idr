module NimService2B

import Data.Maybe
import Data.List
import Data.List1
import Data.SortedMap
import Data.SortedSet
import Data.Strings
import Data.Vect
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser
import Pfsm.Nim
import Pfsm.Service2B

record AppConfig where
  constructor MkAppConfig
  src : String

indentDelta : Nat
indentDelta = 2

%hide Data.Vect.(::)

toNim : Fsm -> String
toNim fsm
  = let name = fsm.name
        pre = camelize name
        events = fsm.events
        ports = fsm.ports
        records = liftRecords fsm.model
        indexes = liftIndexes fsm.model fsm.metas in
        join "\n\n" $ List.filter nonblank [ generateImports name
                                           , generateJsonToRecords records
                                           , generateRecordsToJson records
                                           , generateStringOnlyForRecords records
                                           , generateEqualsToForRecords records
                                           , generatePlayEvent pre events ports
                                           , generateToJson pre fsm.model
                                           , generateFromJson pre fsm.model
                                           , generateDifference pre fsm.model
                                           , generateGetState pre fsm.states
                                           , generateStateFromInt pre fsm.states
                                           , generatePrintState pre fsm.states
                                           , generateIndexKeys pre indexes
                                           , generateSearchable pre fsm.model
                                           , generateFieldValue pre fsm.model
                                           , generateDeepCopy pre fsm.model
                                           , generateMainModule pre name fsm
                                           ]
  where
    generateImports : String -> String
    generateImports name
      = let n = toNimName name in
            List.join "\n" [ "import deques, json, logging, options, service2b, sequtils, strtabs, strutils, times"
                           , "import redis6 except `%`"
                           , "import " ++ n
                           , "import " ++ n ++ "_delegates"
                           ]

    generateJsonToRecords : List Tipe -> String
    generateJsonToRecords ts
      = join "\n\n" $ filter nonblank $ map generateJsonToRecord ts
      where
        generateAssignment : Nat -> Parameter -> String
        generateAssignment idt (n, t, _)
          = (indent idt) ++ (toNimName n) ++ " = " ++ (toNimFromJson ("node{\"" ++ n ++ "\"}") t)

        generateJsonToRecord : Tipe -> String
        generateJsonToRecord (TRecord n ps) = List.join "\n" [ "proc " ++ (toNimName ("json-to-" ++ n)) ++ "(node: JsonNode): " ++ (camelize n) ++ " ="
                                                             , (indent indentDelta) ++ "let"
                                                             , join "\n" $ map (generateAssignment (indentDelta * 2)) ps
                                                             , (indent indentDelta) ++ "result = " ++ (camelize n) ++ "(" ++ (join ", " (map (\(n, _, _) => (toNimName n) ++ ": " ++ (toNimName n)) ps)) ++ ")"
                                                             ]
        generateJsonToRecord _              = ""

    generateRecordsToJson : List Tipe -> String
    generateRecordsToJson ts
      = join "\n\n" $ filter nonblank $ map generateRecordToJson ts
      where
        generateToJson : Nat -> Parameter -> String
        generateToJson idt (n, (TPrimType PTLong), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", % $data." ++ (toNimName n) ++ ")"
        generateToJson idt (n, (TPrimType PTULong), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", % $data." ++ (toNimName n) ++ ")"
        generateToJson idt (n, (TList (TPrimType PTLong)), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ".mapIt($it))"
        generateToJson idt (n, (TList (TPrimType PTULong)), _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ".mapIt($it))"
        generateToJson idt (n, _, _)
          = (indent idt) ++ "result.add(\"" ++ n ++ "\", %data." ++ (toNimName n) ++ ")"

        generateRecordToJson : Tipe -> String
        generateRecordToJson (TRecord n ps)
          = List.join "\n" [ "proc " ++ (toNimName (n ++ "-to-json")) ++ "(data: " ++ (camelize n) ++ "): JsonNode ="
                           , (indent indentDelta) ++ "result = newJObject()"
                           , join "\n" $ map (generateToJson indentDelta) ps
                           ]
        generateRecordToJson _
          = ""

    generateStringOnlyForRecords : List Tipe -> String
    generateStringOnlyForRecords ts
      = join "\n\n" $ filter nonblank $ map generateStringOnlyForRecord ts
      where
        generateStringOnly : Parameter -> String
        generateStringOnly (n, TPrimType PTString, _) = "data." ++ (toNimName n)
        generateStringOnly (n, _,                  _) = "$ data." ++ (toNimName n)

        generateStringOnlyForRecord : Tipe -> String
        generateStringOnlyForRecord (TRecord n ps) = List.join "\n" [ "proc string_only(data: " ++ (camelize n) ++ "): string ="
                                                                    , (indent indentDelta) ++ "result = [" ++ (join ", " $ map generateStringOnly ps) ++ "].join(\" \")"
                                                                    ]
        generateStringOnlyForRecord _              = ""

    generateEqualsToForRecords : List Tipe -> String
    generateEqualsToForRecords ts
      = join "\n\n" $ filter nonblank $ map generateEqualsToForRecord ts
      where
        generateEqualsTo : Nat -> Parameter -> String
        generateEqualsTo idt (n, t, _)
          = List.join "\n" [ (indent idt) ++ "if not equals_to(a." ++ (toNimName n) ++ ", b." ++ (toNimName n) ++ "):"
                           , (indent (idt + indentDelta)) ++ "return false"
                           ]

        generateEqualsToForRecord : Tipe -> String
        generateEqualsToForRecord (TRecord n ps) = List.join "\n" [ "proc equals_to(a, b: " ++ (camelize n) ++ "): bool ="
                                                                  , join "\n" $ map (generateEqualsTo indentDelta) ps
                                                                  , (indent indentDelta) ++ "return true"
                                                                  ]
        generateEqualsToForRecord _              = ""

    generatePlayEvent : String -> List1 Event -> List Port -> String
    generatePlayEvent pre es ps
      = List.join "\n" [ "proc play_event(fsm: " ++ pre ++ "StateMachine, context: ServiceContext, model: " ++ pre ++ "Model, event: string, payload: JsonNode): " ++ pre ++ "Model ="
                       , (indent indentDelta) ++ "case event:"
                       , generateEventHandlers (indentDelta * 2) es ps
                       , (indent (indentDelta * 2)) ++ "else:"
                       , generateDefaultEventHandler (indentDelta * 3)
                       ]
      where
        generateEventHandle : Nat -> List Port -> Event -> String
        generateEventHandle idt ports evt@(MkEvent n ps _)
          = let srcs = [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                       , generateFetchEventArgs (idt + indentDelta) ps
                       , generateEventCall (idt + indentDelta) evt ports
                       ] in
                join "\n" $ List.filter (\x => length x > 0) srcs
          where
            generateFetchEventArg : Nat -> Parameter -> String
            generateFetchEventArg idt (n, t, ms)
              = let lhs = (indent idt) ++ (toNimName n)
                    rhs = case lookup "in-service-context" ms of
                               Just (MVString "true") => "context." ++ (toNimName n)
                               _ => toNimFromJson ("payload{\"" ++ n ++ "\"}") t
                    in
                    lhs ++ " = " ++ rhs

            generateFetchEventArgs : Nat -> List Parameter -> String
            generateFetchEventArgs idt ps
              = let args = map (generateFetchEventArg (idt + indentDelta)) ps in
                    if length args > 0
                       then (indent idt) ++ "let\n" ++ (join "\n" args)
                       else ""

            generateEventCall : Nat -> Event -> List Port -> String
            generateEventCall idt (MkEvent en ps _) ports
              = let params = map (\(n, _, _) => toNimName n) (("fsm", TUnit, Nothing) :: ("context", TUnit, Nothing) :: (("model", (TPrimType PTBool), Nothing) :: ps))
                    portResult = map (\(MkPort pn _) => (toNimName pn) ++"_opt") ports
                    outputCode = map (generateOutputCode idt) ports in
                    List.join "\n" $ List.filter nonblank [ if length ports > 0
                                                               then List.join "\n" [ (indent idt) ++ "let (" ++ (List.join ", " ("newmodel" :: portResult)) ++ ") = " ++ (toNimName en) ++ "(" ++ (List.join ", " params) ++ ")"
                                                                                   , (indent idt) ++ "result = newmodel"
                                                                                   ]
                                                               else (indent idt) ++ "result = " ++ (toNimName en) ++ "(" ++ (List.join ", " params) ++ ")"
                                                          , if length ports > 1
                                                               then (indent idt) ++ "discard context.cache_redis.multi()"
                                                               else ""
                                                          , List.join "\n" outputCode
                                                          , if length ports > 1
                                                               then (indent idt) ++ "discard context.cache_redis.exec()"
                                                               else ""
                                                          ]
              where
                generateOutputCode : Nat -> Port -> String
                generateOutputCode idt (MkPort n _)
                  = List.join "\n" [ (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:"
                                   , (indent (idt + indentDelta)) ++ "output(context, \"" ++ n ++ "\", $ " ++ (toNimName n) ++ "_opt.get)"
                                   ]

        generateEventHandlers : Nat -> List1 Event -> List Port -> String
        generateEventHandlers idt es ps
          = List1.join "\n" $ map (generateEventHandle idt ps) es

        generateDefaultEventHandler : Nat -> String
        generateDefaultEventHandler idt
          = List.join "\n" [ (indent idt) ++ "info \"Unknown event: \" & event"
                           , (indent idt) ++ "info pretty(payload)"
                           , (indent idt) ++ "result = model"
                           ]

    generateToJson : String -> List Parameter -> String
    generateToJson pre ps
      = List.join "\n" [ "proc to_json(model: " ++ pre ++ "Model): JsonNode ="
                       , (indent indentDelta) ++ "result = newJObject()"
                       , join "\n" $ map (generateModelToJson indentDelta) ps
                       ]
      where
        generateModelToJson : Nat -> Parameter -> String
        generateModelToJson idt (n, (TRecord rn _), _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (toNimName (rn ++ "-to-json")) ++ "(model." ++ (toNimName n) ++ "))"
        generateModelToJson idt (n, (TList (TRecord rn _)), _)
          = List.join "\n" [ (indent idt) ++ "let " ++ (toNimName n) ++ " = newJArray()"
                           , (indent idt) ++ "for i in model." ++ (toNimName n) ++ ".mapIt(" ++ (toNimName (rn ++ "-to-json")) ++ "(it)):"
                           , (indent (idt + indentDelta)) ++ (toNimName n) ++ ".add(i)"
                           , (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (toNimName n) ++ ")"
                           ]
        generateModelToJson idt (n, (TList (TPrimType PTLong)), _)
          = List.join "\n" [ (indent idt) ++ "let " ++ (toNimName n) ++ " = newJArray()"
                           , (indent idt) ++ "for i in model." ++ (toNimName n) ++ ".mapIt($it):"
                           , (indent (idt + indentDelta)) ++ (toNimName n) ++ ".add(%i)"
                           , (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (toNimName n) ++ ")"
                           ]
        generateModelToJson idt (n, (TList (TPrimType PTULong)), _)
          = List.join "\n" [ (indent idt) ++ "let " ++ (toNimName n) ++ " = newJArray()"
                           , (indent idt) ++ "for i in model." ++ (toNimName n) ++ ".mapIt($it):"
                           , (indent (idt + indentDelta)) ++ (toNimName n) ++ ".add(%i)"
                           , (indent idt) ++ "result.add(" ++ (show n) ++ ", " ++ (toNimName n) ++ ")"
                           ]
        generateModelToJson idt (n, TPrimType PTLong, _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", % $model." ++ (toNimName n) ++ ")"
        generateModelToJson idt (n, TPrimType PTULong, _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", % $model." ++ (toNimName n) ++ ")"
        generateModelToJson idt (n, _, _)
          = (indent idt) ++ "result.add(" ++ (show n) ++ ", % model." ++ (toNimName n) ++ ")"

    generateFromJson : String -> List Parameter -> String
    generateFromJson pre ps
      = List.join "\n" [ "proc from_json(node: JsonNode): " ++ pre ++ "Model ="
                       , (indent indentDelta) ++ "result = new(" ++ pre ++ "Model)"
                       , generateModelFromJson indentDelta ps
                       ]
      where
        generateAttributeFromJson : Nat -> Parameter -> String
        generateAttributeFromJson idt (n, t, _)
          = let lhs = (indent idt) ++ "result." ++ (toNimName n)
                rhs = toNimFromJson ("node{" ++ (show n) ++"}") t in
                lhs ++ " = " ++ rhs

        generateModelFromJson : Nat -> List Parameter -> String
        generateModelFromJson idt ps = join "\n" $ map (generateAttributeFromJson idt) ps

    generateDifference : String -> List Parameter -> String
    generateDifference pre ps
      = List.join "\n" [ "proc difference(a: " ++ pre ++"Model, b: " ++ pre ++ "Model): seq[string] ="
                       , List.join "\n" $ map (generateDifference' indentDelta) ps
                       ]
      where
        generateCondition : String -> Tipe -> String
        generateCondition n (TDict PTString (TPrimType PTString)) = "equals_to(a." ++ (toNimName n) ++ ", b." ++ (toNimName n) ++ ")"
        generateCondition n (TDict k v)                           = "equals_to[" ++ (toNimType (TPrimType k)) ++ ", " ++ (toNimType v) ++ "](a." ++ (toNimName n) ++ ", b." ++ (toNimName n) ++ ")"
        generateCondition n _                                     = "equals_to(a." ++ (toNimName n) ++ ", b." ++ (toNimName n) ++ ")"

        generateDifference' : Nat -> Parameter -> String
        generateDifference' idt (n, t, _)
          = List.join "\n" [ (indent idt) ++ "if not " ++ (generateCondition n t) ++ ":"
                           , (indent (idt + indentDelta)) ++ "result.add(\"" ++ n ++ "\")"
                           ]

    generateGetState : String -> List1 State -> String
    generateGetState pre ss
      = List.join "\n" [ "proc get_state(model: " ++ pre ++ "Model): int ="
                       , (indent indentDelta) ++ "return model.state"
                       ]

    generateStateFromInt : String -> List1 State -> String
    generateStateFromInt pre ss
      = List.join "\n" [ "proc state_from_int(state: int): Option[" ++ pre ++ "State] ="
                       , (indent indentDelta) ++ "case state:"
                       , List.join "\n" $ map (generateStateFromInt' pre (indentDelta * 2)) $ List.enumerate $ List1.forget ss
                       , (indent (indentDelta * 2)) ++ "else:"
                       , (indent (indentDelta * 3)) ++ "result = none(" ++ pre ++ "State)"
                       ]
      where
        generateStateFromInt' : String -> Nat -> (Nat, State) -> String
        generateStateFromInt' pre idt (idx, (MkState n _ _ _))
          = List.join "\n" [ (indent idt) ++ "of " ++ (show idx) ++ ":"
                           , (indent (idt + indentDelta)) ++ "result = some(" ++ pre ++ "State." ++ (camelize n) ++ ")"
                           ]

    generatePrintState : String -> List1 State -> String
    generatePrintState pre ss
      = List.join "\n" [ "proc `$`(state: " ++ pre ++ "State): string ="
                       , (indent indentDelta) ++ "case state:"
                       , List.join "\n" $ map (generatePrintState' pre (indentDelta * 2)) $ List1.forget ss
                       ]
      where
        generatePrintState' : String -> Nat -> State -> String
        generatePrintState' pre idt (MkState n _ _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ pre ++ "State." ++ (camelize n) ++ ":"
                           , (indent (idt + indentDelta)) ++ "result = \"" ++ n ++ "\""
                           ]

    generateIndexKeys : String -> List Index -> String
    generateIndexKeys pre indexes
      = List.join "\n" [ "proc index_keys(model: " ++ pre ++ "Model): seq[string] ="
                       , (indent indentDelta) ++ "let"
                       , (indent (indentDelta * 2)) ++ "state_opt = state_from_int(model.state)"
                       , (indent (indentDelta * 2)) ++ "state_name = if state_opt.isSome: $ state_opt.get else: \"\""
                       , (indent indentDelta) ++ "result = @["
                       , List.join ",\n" $ map (generateIndexKey (indentDelta * 2)) indexes
                       , (indent indentDelta) ++ "]"
                       ]
      where
        generateIndexKeyFormat : (Nat, Parameter) -> String
        generateIndexKeyFormat (idx, (name, _, _))
          = name ++ "=$" ++ (show (idx + 1))

        generateIndexKeyValue : Parameter -> String
        generateIndexKeyValue ("state", _,                  _) = "state_name"
        generateIndexKeyValue (n,       TPrimType PTChar,   _) = "model." ++ (toNimName n)
        generateIndexKeyValue (n,       TPrimType PTString, _) = "model." ++ (toNimName n)
        generateIndexKeyValue (n,       _,                  _) = "$ model." ++ (toNimName n)

        generateIndexKey : Nat -> Index -> String
        generateIndexKey idt (MkIndex _ fs)
          = let format = List.join "/" $ map generateIndexKeyFormat $ List.enumerate fs
                value = List.join ", " $ map generateIndexKeyValue fs in
                if length fs > 1
                   then (indent idt) ++ "\"" ++ format ++ "\" % [" ++ value ++ "]"
                   else (indent idt) ++ "\"" ++ format ++ "\" % " ++ value

    generateSearchable : String -> List Parameter -> String
    generateSearchable pre params
      = let fs = liftFullTextSearchFields params in
            List.join "\n" [ "proc searchable(): seq[string] ="
                           , (indent indentDelta) ++ "return @[" ++ (List.join ", " $ map (\(n, _, _) => "\"" ++ n ++ "\"") fs) ++ "]"
                           ]

    generateFieldValue : String -> List Parameter -> String
    generateFieldValue pre params
      = List.join "\n" [ "proc field_value(model: " ++ pre ++ "Model, field: string): string ="
                       , (indent indentDelta) ++ "case field:"
                       , List.join "\n" $ map (generateFieldValueCase (indentDelta * 2)) params
                       , (indent (indentDelta * 2)) ++ "else:"
                       , (indent (indentDelta * 3)) ++ "return \"\""
                       ]
      where
        generateFieldValueCase : Nat -> Parameter -> String
        generateFieldValueCase idt (n, TList _, _)
          = List.join "\n" [ (indent idt) ++ "of \"" ++ n ++ "\":"
                           , (indent (idt + indentDelta)) ++ "return model." ++ (toNimName n) ++ ".mapIt(string_only(it)).join(\" \")"
                           ]
        generateFieldValueCase idt (n, _, _)
          = List.join "\n" [ (indent idt) ++ "of \"" ++ n ++ "\":"
                           , (indent (idt + indentDelta)) ++ "return string_only model." ++ (toNimName n)
                           ]

    generateDeepCopy : String -> List Parameter -> String
    generateDeepCopy pre params
      = List.join "\n" [ "proc deep_copy(model: " ++ pre ++ "Model): " ++ pre ++ "Model ="
                       , (indent indentDelta) ++ pre ++ "Model("
                       , List.join "\n" $ map (\(n, _, _) => (indent (indentDelta * 2)) ++ (toNimName n) ++ ": model." ++ (toNimName n) ++ ",") params
                       , (indent indentDelta) ++ ")"
                       ]

    generateMainModule : String -> String -> Fsm -> String
    generateMainModule pre name fsm
      = let env = rootEnv fsm
            model = fsm.model
            actions = nubBy outputActionEqualityChecker $ liftOutputActions fsm.states fsm.transitions in
            join "\n\n" $ List.filter nonblank [ "when isMainModule:"
                                               , generateNonDefaultOutputDelegates indentDelta pre name env model actions
                                               , generateDefaultOutputDelegates indentDelta pre name env model actions
                                               , generateMainCode indentDelta pre name env fsm
                                               ]
      where
        defaultOutputActionFilter : Action -> Bool
        defaultOutputActionFilter (OutputAction (MkPort "response" _) _) = True
        defaultOutputActionFilter _                                      = False

        generateOutputDelegate : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> (Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String) -> Action -> String
        generateOutputDelegate idt pre name env model body (OutputAction (MkPort pn pt) es)
          = let funname = "output_" ++ (toNimName pn)
                indexedParameters = enumerate $ map (\x => fromMaybe TUnit $ inferType env x) es
                retType = toNimType $ returnType pt in
                List.join "\n" [ (indent idt) ++ "proc " ++ funname ++ "(" ++ (List.join ", " (map (\(n', t) => (toNimName n') ++ ": " ++ (toNimType t)) (("ctx", TRecord "ServiceContext" []) :: ("model", TRecord (pre ++ "Model") []) :: (map (\(i, t) => ("a" ++ show i, t)) indexedParameters)))) ++ "): " ++ retType ++ " ="
                               , body (idt + indentDelta) name funname indexedParameters model
                               ]
        generateOutputDelegate idt env pre name model body _ = ""

        generateNonDefaultOutputDelegates : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> List Action -> String
        generateNonDefaultOutputDelegates idt pre name env model as
          = join "\n\n" $ filter nonblank $ map (generateOutputDelegate idt pre name env model bodyGenerator) $ filter (not . defaultOutputActionFilter) as
          where
            bodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            bodyGenerator idt name funname indexedParameters model
              = (indent idt) ++ (toNimName name) ++ "_" ++ funname ++ "(" ++ (foldl (\acc, (i, _) => acc ++ ", a" ++ (show i)) "ctx, model" indexedParameters) ++ ")"

        generateDefaultOutputDelegates : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> List Action -> String
        generateDefaultOutputDelegates idt pre name env model as
          = join "\n\n" $ filter nonblank $ map (generateDefaultOutputDelegate idt pre name env model) $ filter defaultOutputActionFilter as
          where
            responseBodyGenerator : Nat -> String -> String -> List (Nat, Tipe) -> List Parameter -> String
            responseBodyGenerator idt name funname _ _
              = (indent idt) ++ "return \"{\\\"code\\\":\" & $a0 & \",\\\"payload\\\":\\\"\" & a1 & \"\\\",\\\"callback\\\":\\\"\" & $ctx.callback & \"\\\",\\\"fsmid\\\":\\\"\" & $ctx.fsmid & \"\\\"}\""

            generateDefaultOutputDelegate : Nat -> String -> String -> SortedMap Expression Tipe -> List Parameter -> Action -> String
            generateDefaultOutputDelegate idt pre name env model act@(OutputAction (MkPort "response" _) _)
              = generateOutputDelegate idt pre name env model responseBodyGenerator act
            generateDefaultOutputDelegate idt pre name env model _
              = ""

        generateMainCode : Nat -> String -> String -> SortedMap Expression Tipe -> Fsm -> String
        generateMainCode idt pre name env fsm
          = let aas = nubBy assignmentActionEqualityChecker $ liftAssignmentActions fsm.states fsm.transitions
                oas = liftOutputActions fsm.states fsm.transitions
                aes = nubBy (applicationExpressionEqualityChecker env) $ filter applicationExpressionFilter $ flatten $ map expressionsOfAction (aas ++ oas)
                ges = nubBy (applicationExpressionEqualityChecker env) $ filter applicationExpressionFilter $ flatten $ map expressionsOfTestExpression $ flatten $ List1.forget $ map guardsOfTransition fsm.transitions in
                List.join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                      , generateInitActionDelegates (idt + indentDelta) pre name aes
                                                      , generateInitOutputDelegates (idt + indentDelta) pre $ nubBy outputActionEqualityChecker oas
                                                      , generateInitGuardDelegates (idt + indentDelta) pre name ges
                                                      , generateInitStateMachine (idt + indentDelta) pre (length aes > Z) (length oas > Z) (length ges > Z)
                                                      , generateInitServiceDelegate (idt + indentDelta) pre
                                                      , (indent idt) ++ "run[" ++ pre ++ "StateMachine[ServiceContext], " ++ pre ++ "Model](bfsm, \"%%NAME%%\", \"%%INPUT-QUEUE%%\", \"%%OUTPUT-QUEUE%%\", delegate)"
                                                      ]
          where

            generateInitActionDelegates : Nat -> String -> String -> List Expression -> String
            generateInitActionDelegates idt pre name []  = ""
            generateInitActionDelegates idt pre name aes = List.join "\n" [ (indent idt) ++ "action_delegate = " ++ pre ++ "ActionDelegate[ServiceContext]("
                                                                          , join ",\n" $ map (generateInitActionDelegate (idt + indentDelta) name) aes
                                                                          , (indent idt) ++ ")"
                                                                          ]
              where
                toActionFuncName : Name -> String
                toActionFuncName "+" = "plus"
                toActionFuncName "-" = "minus"
                toActionFuncName "*" = "multiplay"
                toActionFuncName "/" = "divide"
                toActionFuncName n   = toNimName n

                generateInitActionDelegate : Nat -> String -> Expression -> String
                generateInitActionDelegate idt name (ApplicationExpression n _) = (indent idt) ++ (toNimFuncName n) ++ ": " ++ (toNimName name) ++ "_action_" ++ (toActionFuncName n)
                generateInitActionDelegate idt name _                           = ""

            generateInitOutputDelegates : Nat -> String -> List Action -> String
            generateInitOutputDelegates idt pre [] = ""
            generateInitOutputDelegates idt pre as = List.join "\n" [ (indent idt) ++ "output_delegate = " ++ pre ++ "OutputDelegate[ServiceContext]("
                                                                    , join ",\n" $ map (generateInitOutputDelegate (idt + indentDelta)) as
                                                                    , (indent idt) ++ ")"
                                                                    ]
              where
                generateInitOutputDelegate : Nat -> Action -> String
                generateInitOutputDelegate idt (OutputAction (MkPort n _) _) = (indent idt) ++ (toNimName n) ++ ": output_" ++ (toNimName n)
                generateInitOutputDelegate idt _ = ""

            generateInitGuardDelegates : Nat -> String -> String -> List Expression -> String
            generateInitGuardDelegates idt pre name [] = ""
            generateInitGuardDelegates idt pre name es = List.join "\n" [ (indent idt) ++ "guard_delegate = " ++ pre ++ "GuardDelegate("
                                                                        , join ",\n" $ map (generateInitGuardDelegate (idt + indentDelta) name) es
                                                                        , (indent idt) ++ ")"
                                                                        ]
              where
                generateInitGuardDelegate : Nat -> String -> Expression -> String
                generateInitGuardDelegate idt name (ApplicationExpression n _) = (indent idt) ++ (toNimName n) ++ ": " ++ name ++ "_guard_" ++ (toNimName n)
                generateInitGuardDelegate idt name _ = ""

            generateInitStateMachine : Nat -> String -> Bool -> Bool -> Bool -> String
            generateInitStateMachine idt pre ad od gd
              = let code = [ (indent idt) ++ "bfsm = new" ++ pre ++ "StateMachine[ServiceContext]("
                           , if ad then (indent (idt + indentDelta)) ++ "action_delegate," else ""
                           , if od then (indent (idt + indentDelta)) ++ "output_delegate," else ""
                           , if gd then (indent (idt + indentDelta)) ++ "guard_delegate," else ""
                           , (indent idt) ++ ")"
                           ] in
                    List.join "\n" $ List.filter (\x => length x > Z) code

            generateInitServiceDelegate : Nat -> String -> String
            generateInitServiceDelegate idt pre
              = List.join "\n" [ (indent idt) ++ "delegate = ServiceDelegate[" ++ pre ++ "StateMachine[ServiceContext], " ++ pre ++ "Model]("
                               , (indent (idt + indentDelta)) ++ "play_event: play_event,"
                               , (indent (idt + indentDelta)) ++ "from_json: from_json,"
                               , (indent (idt + indentDelta)) ++ "to_json: to_json,"
                               , (indent (idt + indentDelta)) ++ "difference: difference,"
                               , (indent (idt + indentDelta)) ++ "get_state: get_state,"
                               , (indent (idt + indentDelta)) ++ "index_keys: index_keys,"
                               , (indent (idt + indentDelta)) ++ "searchable: searchable,"
                               , (indent (idt + indentDelta)) ++ "field_value: field_value,"
                               , (indent (idt + indentDelta)) ++ "deep_copy: deep_copy,"
                               , (indent idt) ++ ")"
                               ]

doWork : AppConfig -> IO ()
doWork conf
  = do Right fsm <- loadFsmFromFile conf.src
       | Left err => putStrLn $ err
       putStrLn $ toNim fsm

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing
  where
    parseArgs' : Maybe String -> List String -> Maybe AppConfig
    parseArgs' Nothing    []        = Nothing
    parseArgs' (Just src) []        = Just (MkAppConfig src)
    parseArgs' _          (x :: xs) = parseArgs' (Just x) xs

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-nim-service2b <src>"
                   , ""
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
