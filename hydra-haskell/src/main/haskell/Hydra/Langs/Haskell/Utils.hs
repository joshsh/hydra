module Hydra.Langs.Haskell.Utils where

import Hydra.Kernel
import Hydra.Langs.Haskell.Language
import qualified Hydra.Langs.Haskell.Ast as H
import qualified Hydra.Lib.Strings as Strings

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S


data Namespaces = Namespaces {
  namespacesFocus :: (Namespace, H.ModuleName),
  namespacesMapping :: M.Map Namespace H.ModuleName} deriving Show

applicationPattern name args = H.PatternApplication $ H.Pattern_Application name args

elementReference :: Namespaces -> Name -> H.Name
elementReference (Namespaces (gname, H.ModuleName gmod) namespaces) name = case (qualifiedNameNamespace qname) of
    Nothing -> simpleName local
    Just ns -> case M.lookup ns namespaces of
      Nothing -> simpleName local
      Just (H.ModuleName a) -> if ns == gname
         then simpleName escLocal
         else rawName $ a ++ "." ++ escLocal
  where
    qname = qualifyNameEager name
    local = qualifiedNameLocal qname
    escLocal = sanitizeHaskellName local
    simple = simpleName $ qualifiedNameLocal qname

hsapp :: H.Expression -> H.Expression -> H.Expression
hsapp l r = H.ExpressionApplication $ H.Expression_Application l r

hslambda :: String -> H.Expression -> H.Expression
hslambda v rhs = H.ExpressionLambda (H.Expression_Lambda [H.PatternName $ rawName v] rhs)

hslit :: H.Literal -> H.Expression
hslit = H.ExpressionLiteral

hsPrimitiveReference :: Name -> H.Name
hsPrimitiveReference name = H.NameNormal $ H.QualifiedName [prefix] $ H.NamePart local
  where
    QualifiedName (Just (Namespace ns)) local = qualifyNameEager name
    prefix = H.NamePart $ capitalize $ L.last $ Strings.splitOn "/" ns

hsvar :: String -> H.Expression
hsvar s = H.ExpressionVariable $ rawName s

namespacesForModule :: Module -> Flow Graph Namespaces
namespacesForModule mod = do
    nss <- moduleDependencyNamespaces True True True True mod
    return $ Namespaces focusPair $ fst $ L.foldl addPair (M.empty, S.empty) (toPair <$> S.toList nss)
  where
    ns = moduleNamespace mod
    focusPair = toPair ns
    toModuleName (Namespace n) = H.ModuleName $ capitalize $ L.last $ Strings.splitOn "/" n
    toPair name = (name, toModuleName name)
    addPair (m, s) (name, alias@(H.ModuleName aliasStr)) = if S.member alias s
      then addPair (m, s) (name, H.ModuleName $ aliasStr ++ "_")
      else (M.insert name alias m, S.insert alias s)

newtypeAccessorName :: Name -> String
newtypeAccessorName name = "un" ++ localNameOfEager name

rawName :: String -> H.Name
rawName n = H.NameNormal $ H.QualifiedName [] $ H.NamePart n

recordFieldReference :: Namespaces -> Name -> Name -> H.Name
recordFieldReference namespaces sname (Name fname) = elementReference namespaces $
    unqualifyName $ QualifiedName (qualifiedNameNamespace $ qualifyNameEager sname) nm
  where
    nm = decapitalize (typeNameForRecord sname) ++ capitalize fname

sanitizeHaskellName :: String -> String
sanitizeHaskellName = sanitizeWithUnderscores reservedWords

simpleName :: String -> H.Name
simpleName = rawName . sanitizeHaskellName

simpleValueBinding :: H.Name -> H.Expression -> Maybe H.LocalBindings -> H.ValueBinding
simpleValueBinding hname rhs bindings = H.ValueBindingSimple $ H.ValueBinding_Simple pat (H.RightHandSide rhs) bindings
  where
    pat = H.PatternApplication $ H.Pattern_Application hname []

toTypeApplication :: [H.Type] -> H.Type
toTypeApplication = app . L.reverse
  where
    app l = case l of
      [e] -> e
      (h:r) -> H.TypeApplication $ H.Type_Application (app r) h

typeNameForRecord :: Name -> String
typeNameForRecord (Name sname) = L.last (Strings.splitOn "." sname)

unionFieldReference :: Namespaces -> Name -> Name -> H.Name
unionFieldReference namespaces sname (Name fname) = elementReference namespaces $
    unqualifyName $ QualifiedName ns nm
  where
    ns = qualifiedNameNamespace $ qualifyNameEager sname
    nm = capitalize (typeNameForRecord sname) ++ capitalize fname

unpackLambdaType :: Graph -> Type -> ([Name], Type)
unpackLambdaType cx t = case stripType t of
  TypeLambda (LambdaType v tbody) -> (v:vars, t')
    where
      (vars, t') = unpackLambdaType cx tbody
  _ -> ([], t)
