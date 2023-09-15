module Hydra.Langs.Scala.Coder (moduleToScala) where

import Hydra.Kernel
import Hydra.Dsl.Terms
import Hydra.Langs.Scala.Language
import Hydra.Langs.Scala.Utils
import Hydra.Adapters
import Hydra.Tools.Serialization
import Hydra.Langs.Scala.Serde
import qualified Hydra.Dsl.Types as Types
import qualified Hydra.Langs.Scala.Meta as Scala
import qualified Hydra.Lib.Strings as Strings

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


moduleToScala :: Module Kv -> Flow (Graph Kv) (M.Map FilePath String)
moduleToScala mod = do
  pkg <- moduleToScalaPackage mod
  let s = printExpr $ parenthesize $ writePkg pkg
  return $ M.fromList [(namespaceToFilePath False (FileExtension "scala") $ moduleNamespace mod, s)]

moduleToScalaPackage :: Module Kv -> Flow (Graph Kv) Scala.Pkg
moduleToScalaPackage = transformModule scalaLanguage encodeUntypedTerm constructModule

constructModule :: Module Kv -> M.Map (Type Kv) (Coder (Graph Kv) (Graph Kv) (Term) Scala.Data) -> [(Element Kv, TypedTerm)]
  -> Flow (Graph Kv) Scala.Pkg
constructModule mod coders pairs = do
    defs <- CM.mapM toDef pairs
    let pname = toScalaName $ h $ moduleNamespace mod
    let pref = Scala.Data_RefName pname
    imports <- findImports
    return $ Scala.Pkg pname pref (imports ++ defs)
  where
    h (Namespace n) = n
    findImports = do
        elImps <- moduleDependencyNamespaces False False True False mod
        primImps <- moduleDependencyNamespaces False True False False mod
        return $ (toElImport <$> S.toList elImps) ++ (toPrimImport <$> S.toList primImps)
      where
        toElImport (Namespace ns) = Scala.StatImportExport $ Scala.ImportExportStatImport $ Scala.Import [
          Scala.Importer (Scala.Data_RefName $ toScalaName ns) [Scala.ImporteeWildcard]]
        toPrimImport (Namespace ns) = Scala.StatImportExport $ Scala.ImportExportStatImport $ Scala.Import [
          Scala.Importer (Scala.Data_RefName $ toScalaName ns) []]
    toScalaName name = Scala.Data_Name $ Scala.PredefString $ L.intercalate "." $ Strings.splitOn "/" name
    toDef (el, TypedTerm typ term) = withTrace ("element " ++ unName (elementName el)) $ do
        let coder = Y.fromJust $ M.lookup typ coders
        rhs <- coderEncode coder term
        Scala.StatDefn <$> case rhs of
          Scala.DataApply _ -> toVal rhs
          Scala.DataFunctionData fun -> case stripType typ of
            TypeFunction (FunctionType _ cod) -> toDefn fun cod
            _ -> fail $ "expected function type, but found " ++ show typ
          Scala.DataLit _ -> toVal rhs
          Scala.DataRef _ -> toVal rhs -- TODO
          _ -> fail $ "unexpected RHS: " ++ show rhs
      where
        lname = localNameOfEager $ elementName el

        freeTypeVars = S.toList $ freeVariablesInType typ

        toDefn (Scala.Data_FunctionDataFunction (Scala.Data_Function params body)) cod = do
          let tparams = stparam <$> freeTypeVars
          scod <- encodeType cod
          return $ Scala.DefnDef $ Scala.Defn_Def []
            (Scala.Data_Name $ Scala.PredefString lname) tparams [params] (Just scod) body

        toVal rhs = pure $ Scala.DefnVal $ Scala.Defn_Val [] [namePat] Nothing rhs
          where
            namePat = Scala.PatVar $ Scala.Pat_Var $ Scala.Data_Name $ Scala.PredefString lname

encodeFunction :: Kv -> Function Kv -> Y.Maybe (Term) -> Flow (Graph Kv) Scala.Data
encodeFunction meta fun arg = case fun of
    FunctionLambda (Lambda (Name v) body) -> slambda v <$> encodeTerm body <*> findSdom
    FunctionPrimitive name -> pure $ sprim name
    FunctionElimination e -> case e of
      EliminationWrap name -> pure $ sname $ "ELIM-NOMINAL(" ++ show name ++ ")" -- TODO
      EliminationOptional c -> pure $ sname "ELIM-OPTIONAL" -- TODO
      EliminationRecord p -> fail "unapplied projection not yet supported"
      EliminationUnion (CaseStatement _ def cases) -> do
          let v = "v"
          dom <- findDomain
          ftypes <- withSchemaContext $ fieldTypes dom
          cx <- getState
          let sn = nameOfType cx dom
          scases <- CM.mapM (encodeCase ftypes sn) cases
          -- TODO: default
          case arg of
            Nothing -> slambda v <$> pure (Scala.DataMatch $ Scala.Data_Match (sname v) scases) <*> findSdom
            Just a -> do
              sa <- encodeTerm a
              return $ Scala.DataMatch $ Scala.Data_Match sa scases
        where
          encodeCase ftypes sn f@(Field fname fterm) = do
  --            dom <- findDomain (termMeta fterm)           -- Option #1: use type inference
              let dom = Y.fromJust $ M.lookup fname ftypes -- Option #2: look up the union type
              let patArgs = if dom == Types.unit then [] else [svar v]
              -- Note: PatExtract has the right syntax, though this may or may not be the Scalameta-intended way to use it
              let pat = Scala.PatExtract $ Scala.Pat_Extract (sname $ qualifyUnionFieldName "MATCHED." sn fname) patArgs
              body <- encodeTerm $ applyVar fterm v
              return $ Scala.Case pat Nothing body
            where
              v = Name "y"
          applyVar fterm avar@(Name v) = case stripTerm fterm of
            TermFunction (FunctionLambda (Lambda v1 body)) -> if isFreeIn v1 body
              then body
              else substituteVariable v1 avar body
            _ -> apply fterm (var v)
  where
    findSdom = Just <$> (findDomain >>= encodeType)
    findDomain = do
        cx <- getState
        r <- annotationClassTypeOf (graphAnnotations cx) meta
        case r of
          Nothing -> fail "expected a typed term"
          Just t -> domainOf t
      where
        domainOf t = case stripType t of
          TypeFunction (FunctionType dom _) -> pure dom
          _ -> fail $ "expected a function type, but found " ++ show t

encodeLiteral :: Literal -> Flow (Graph Kv) Scala.Lit
encodeLiteral av = case av of
    LiteralBoolean b -> pure $ Scala.LitBoolean b
    LiteralFloat fv -> case fv of
      FloatValueFloat32 f -> pure $ Scala.LitFloat f
      FloatValueFloat64 f -> pure $ Scala.LitDouble f
      _ -> unexpected "floating-point number" $ show fv
    LiteralInteger iv -> case iv of
      IntegerValueInt16 i -> pure $ Scala.LitShort $ fromIntegral i
      IntegerValueInt32 i -> pure $ Scala.LitInt i
      IntegerValueInt64 i -> pure $ Scala.LitLong $ fromIntegral i
      IntegerValueUint8 i -> pure $ Scala.LitByte $ fromIntegral i
      _ -> unexpected "integer" $ show iv
    LiteralString s -> pure $ Scala.LitString s
    _ -> unexpected "literal value" $ show av

encodeTerm :: Term -> Flow (Graph Kv) Scala.Data
encodeTerm term = case stripTerm term of
    TermApplication (Application fun arg) -> case stripTerm fun of
        TermFunction f -> case f of
          FunctionElimination e -> case e of
            EliminationWrap name -> fallback
            EliminationOptional c -> fallback
            EliminationRecord (Projection _ (FieldName fname)) -> do
              sarg <- encodeTerm arg
              return $ Scala.DataRef $ Scala.Data_RefSelect $ Scala.Data_Select sarg
                (Scala.Data_Name $ Scala.PredefString fname)
            EliminationUnion _ -> do
              cx <- getState
              encodeFunction (termMeta cx fun) f (Just arg)
          _ -> fallback
        _ -> fallback
      where
        fallback = sapply <$> encodeTerm fun <*> ((: []) <$> encodeTerm arg)
    TermFunction f -> do
      cx <- getState
      encodeFunction (termMeta cx term) f Nothing
    TermList els -> sapply (sname "Seq") <$> CM.mapM encodeTerm els
    TermLiteral v -> Scala.DataLit <$> encodeLiteral v
    TermMap m -> sapply (sname "Map") <$> CM.mapM toPair (M.toList m)
      where
        toPair (k, v) = sassign <$> encodeTerm k <*> encodeTerm v
    TermWrap (Nominal _ term') -> encodeTerm term'
    TermOptional m -> case m of
      Nothing -> pure $ sname "None"
      Just t -> (\s -> sapply (sname "Some") [s]) <$> encodeTerm t
    TermRecord (Record name fields) -> do
      let n = scalaTypeName False name
      args <- CM.mapM encodeTerm (fieldTerm <$> fields)
      return $ sapply (sname n) args
    TermSet s -> sapply (sname "Set") <$> CM.mapM encodeTerm (S.toList s)
    TermUnion (Injection sn (Field fn ft)) -> do
      let lhs = sname $ qualifyUnionFieldName "UNION." (Just sn) fn
      args <- case stripTerm ft of
        TermRecord (Record _ []) -> pure []
        _ -> do
          arg <- encodeTerm ft
          return [arg]
      return $ sapply lhs args
    TermVariable (Name v) -> pure $ sname v
    _ -> fail $ "unexpected term: " ++ show term


encodeType :: Type Kv -> Flow (Graph Kv) Scala.Type
encodeType t = case stripType t of
  TypeFunction (FunctionType dom cod) -> do
    sdom <- encodeType dom
    scod <- encodeType cod
    return $ Scala.TypeFunctionType $ Scala.Type_FunctionTypeFunction $ Scala.Type_Function [sdom] scod
  TypeList lt -> stapply1 <$> pure (stref "Seq") <*> encodeType lt
  TypeLiteral lt -> case lt of
--    TypeBinary ->
    LiteralTypeBoolean -> pure $ stref "Boolean"
    LiteralTypeFloat ft -> case ft of
--      FloatTypeBigfloat ->
      FloatTypeFloat32 -> pure $ stref "Float"
      FloatTypeFloat64 -> pure $ stref "Double"
    LiteralTypeInteger it -> case it of
--      IntegerTypeBigint ->
--      IntegerTypeInt8 ->
      IntegerTypeInt16 -> pure $ stref "Short"
      IntegerTypeInt32 -> pure $ stref "Int"
      IntegerTypeInt64 -> pure $ stref "Long"
      IntegerTypeUint8 -> pure $ stref "Byte"
--      IntegerTypeUint16 ->
--      IntegerTypeUint32 ->
--      IntegerTypeUint64 ->
    LiteralTypeString -> pure $ stref "String"
  TypeMap (MapType kt vt) -> stapply2 <$> pure (stref "Map") <*> encodeType kt <*> encodeType vt
  TypeOptional ot -> stapply1 <$> pure (stref "Option") <*> encodeType ot
--  TypeRecord sfields ->
  TypeSet st -> stapply1 <$> pure (stref "Set") <*> encodeType st
--  TypeUnion sfields ->
  TypeLambda (LambdaType v body) -> do
    sbody <- encodeType body
    return $ Scala.TypeLambda $ Scala.Type_Lambda [stparam v] sbody
--   TypeVariable name -> pure $ stref $ scalaTypeName True name
  TypeVariable (Name v) -> pure $ Scala.TypeVar $ Scala.Type_Var $ Scala.Type_Name v
  _ -> fail $ "can't encode unsupported type in Scala: " ++ show t

encodeUntypedTerm :: Term -> Flow (Graph Kv) Scala.Data
encodeUntypedTerm term = annotateTermWithTypes term >>= encodeTerm
