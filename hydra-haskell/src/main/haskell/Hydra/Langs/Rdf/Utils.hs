module Hydra.Langs.Rdf.Utils where

import Hydra.Kernel
import qualified Hydra.Langs.Rdf.Syntax as Rdf

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S


descriptionsToGraph :: [Rdf.Description] -> Rdf.Graph
descriptionsToGraph ds = Rdf.Graph $ S.fromList $ triplesOf ds

emptyDescription :: Rdf.Node -> Rdf.Description
emptyDescription node = Rdf.Description node emptyGraph

emptyGraph :: Rdf.Graph
emptyGraph = Rdf.Graph S.empty

emptyLangStrings :: Rdf.LangStrings
emptyLangStrings = Rdf.LangStrings M.empty

encodeLiteral :: Literal -> Flow (Graph) Rdf.Literal
encodeLiteral lit = case lit of
    LiteralBinary s -> fail "base 64 encoding not yet implemented"
    LiteralBoolean b -> pure $ xsd (\b -> if b then "true" else "false") b "boolean"
    LiteralFloat f -> pure $ case f of
      FloatValueBigfloat v -> xsd show v "decimal"
      FloatValueFloat32 v -> xsd show v "float"
      FloatValueFloat64 v -> xsd show v "double"
    LiteralInteger i -> pure $ case i of
      IntegerValueBigint v -> xsd show v "integer"
      IntegerValueInt8 v   -> xsd show v "byte"
      IntegerValueInt16 v  -> xsd show v "short"
      IntegerValueInt32 v  -> xsd show v "int"
      IntegerValueInt64 v  -> xsd show v "long"
      IntegerValueUint8 v  -> xsd show v "unsignedByte"
      IntegerValueUint16 v -> xsd show v "unsignedShort"
      IntegerValueUint32 v -> xsd show v "unsignedInt"
      IntegerValueUint64 v -> xsd show v "unsignedLong"
    LiteralString s -> pure $ xsd id s "string"
  where
    -- TODO: using Haskell's built-in show function is a cheat, and may not be correct/optimal in all cases
    xsd ser x local = Rdf.Literal (ser x) (xmlSchemaDatatypeIri local) Nothing

forObjects :: Rdf.Resource -> Rdf.Iri -> [Rdf.Node] -> [Rdf.Triple]
forObjects subj pred objs = (Rdf.Triple subj pred) <$> objs

iri :: String -> String -> Rdf.Iri
iri ns local = Rdf.Iri $ ns ++ local

keyIri :: String -> Rdf.Iri
keyIri = iri "urn:key:" -- Note: not an official URN scheme

mergeGraphs :: [Rdf.Graph] -> Rdf.Graph
mergeGraphs graphs = Rdf.Graph $ L.foldl S.union S.empty (Rdf.unGraph <$> graphs)

nameToIri :: Name -> Rdf.Iri
nameToIri name = Rdf.Iri $ "urn:" ++ unName name

nextBlankNode :: Flow (Graph) Rdf.Resource
nextBlankNode = do
  count <- nextCount "rdfBlankNodeCounter"
  return $ Rdf.ResourceBnode $ Rdf.BlankNode $ "b" ++ show count

-- Note: these are not "proper" URNs, as they do not use an established URN scheme
propertyIri :: Name -> FieldName -> Rdf.Iri
propertyIri rname fname = Rdf.Iri $ "urn:" ++ unNamespace gname ++ "#" ++ decapitalize local ++ capitalize (unFieldName fname)
  where
    QualifiedName (Just gname) local = qualifyNameLazy rname

rdfIri :: String -> Rdf.Iri
rdfIri = iri "http://www.w3.org/1999/02/22-rdf-syntax-ns#"

resourceToNode :: Rdf.Resource -> Rdf.Node
resourceToNode r = case r of
  Rdf.ResourceIri i -> Rdf.NodeIri i
  Rdf.ResourceBnode b -> Rdf.NodeBnode b

subjectsOf :: [Rdf.Description] -> [Rdf.Node]
subjectsOf descs = Rdf.descriptionSubject <$> descs

triplesOf :: [Rdf.Description] -> [Rdf.Triple]
triplesOf descs = L.concat ((S.toList . Rdf.unGraph . Rdf.descriptionGraph) <$> descs)

xmlSchemaDatatypeIri :: String -> Rdf.Iri
xmlSchemaDatatypeIri = iri "http://www.w3.org/2001/XMLSchema#"
