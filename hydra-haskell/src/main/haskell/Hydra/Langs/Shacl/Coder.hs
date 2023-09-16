module Hydra.Langs.Shacl.Coder where

import Hydra.Kernel
import Hydra.Langs.Rdf.Utils
import qualified Hydra.Langs.Rdf.Syntax as Rdf
import qualified Hydra.Langs.Shacl.Model as Shacl
import qualified Hydra.Dsl.Literals as Literals
import qualified Hydra.Dsl.Expect as Expect
import qualified Hydra.Dsl.Terms as Terms

import qualified Control.Monad as CM
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


shaclCoder :: Module -> Flow (Graph) (Shacl.ShapesGraph, Graph -> Flow (Graph) Rdf.Graph)
shaclCoder mod = do
    g <- getState
    -- Note: untested since deprecation of element schemas
    typeEls <- CM.filterM (isType g) $ moduleElements mod
    shapes <- CM.mapM toShape typeEls
    let sg = Shacl.ShapesGraph $ S.fromList shapes
    let termFlow = \g -> do
          fail "not implemented"
    return (sg, termFlow)
  where
    isType g el = do
      typ <- requireTermType $ elementData el
      return $ stripType typ == TypeVariable _Type
    toShape el = do
      typ <- coreDecodeType $ elementData el
      common <- encodeType typ
      return $ Shacl.Definition (elementIri el) $ Shacl.ShapeNode $ Shacl.NodeShape common

common :: [Shacl.CommonConstraint] -> Shacl.CommonProperties
common constraints = defaultCommonProperties {
  Shacl.commonPropertiesConstraints = S.fromList constraints}

defaultCommonProperties :: Shacl.CommonProperties
defaultCommonProperties = Shacl.CommonProperties {
  Shacl.commonPropertiesConstraints = S.empty,
  Shacl.commonPropertiesDeactivated = Nothing,
  Shacl.commonPropertiesMessage = emptyLangStrings,
  Shacl.commonPropertiesSeverity = Shacl.SeverityInfo,
  Shacl.commonPropertiesTargetClass = S.empty,
  Shacl.commonPropertiesTargetNode = S.empty,
  Shacl.commonPropertiesTargetObjectsOf = S.empty,
  Shacl.commonPropertiesTargetSubjectsOf = S.empty}

elementIri :: Element -> Rdf.Iri
elementIri = nameToIri . elementName

encodeField :: Name -> Rdf.Resource -> Field -> Flow (Graph) [Rdf.Triple]
encodeField rname subject field = do
  node <- nextBlankNode
  descs <- encodeTerm node (fieldTerm field)
  return $ triplesOf descs ++
    forObjects subject (propertyIri rname $ fieldName field) (subjectsOf descs)

encodeFieldType :: Name -> Maybe Integer -> FieldType -> Flow (Graph) (Shacl.Definition Shacl.PropertyShape)
encodeFieldType rname order (FieldType fname ft) = do
    shape <- forType (Just 1) (Just 1) ft
    return $ Shacl.Definition iri shape
  where
    iri = propertyIri rname fname
    forType mn mx t = case stripType t of
      TypeOptional ot -> forType (Just 0) mx ot
      TypeSet st -> forType mn Nothing st
      _ -> do
        cp <- encodeType t
        let baseProp = property iri
        return $ baseProp {
          Shacl.propertyShapeCommon = cp,
          Shacl.propertyShapeConstraints = S.fromList $ Y.catMaybes [
            Shacl.PropertyShapeConstraintMinCount <$> mn,
            Shacl.PropertyShapeConstraintMaxCount <$> mx],
          Shacl.propertyShapeOrder = order}

encodeLiteralType :: LiteralType -> Shacl.CommonProperties
encodeLiteralType lt = case lt of
    LiteralTypeBinary -> xsd "base64Binary"
    LiteralTypeBoolean -> xsd "boolean"
    LiteralTypeFloat ft -> case ft of
      FloatTypeBigfloat -> xsd "decimal"
      FloatTypeFloat32 -> xsd "float"
      FloatTypeFloat64 -> xsd "double"
    LiteralTypeInteger it -> case it of
      IntegerTypeBigint -> xsd "integer"
      IntegerTypeInt8 -> xsd "byte"
      IntegerTypeInt16 -> xsd "short"
      IntegerTypeInt32 -> xsd "int"
      IntegerTypeInt64 -> xsd "long"
      IntegerTypeUint8 -> xsd "unsignedByte"
      IntegerTypeUint16 -> xsd "unsignedShort"
      IntegerTypeUint32 -> xsd "unsignedInt"
      IntegerTypeUint64 -> xsd "unsignedLong"
    LiteralTypeString -> xsd "string"
  where
    xsd local = common [Shacl.CommonConstraintDatatype $ xmlSchemaDatatypeIri local]

encodeTerm :: Rdf.Resource -> Term -> Flow (Graph) [Rdf.Description]
encodeTerm subject term = case term of
  TermAnnotated (Annotated inner ann) -> encodeTerm subject inner -- TODO: extract an rdfs:comment
  TermList terms -> encodeList subject terms
    where
      encodeList subj terms = if L.null terms
        then pure [emptyDescription $ (Rdf.NodeIri $ rdfIri "nil")]
          else do
            node <- nextBlankNode
            fdescs <- encodeTerm node $ L.head terms
            let firstTriples = triplesOf fdescs ++
                  forObjects subj (rdfIri "first") (subjectsOf fdescs)
            next <- nextBlankNode
            rdescs <- encodeList next $ L.tail terms
            let restTriples = triplesOf rdescs ++
                  forObjects subj (rdfIri "rest") (subjectsOf rdescs)
            return [Rdf.Description (resourceToNode subj) (Rdf.Graph $ S.fromList $ firstTriples ++ restTriples)]
  TermLiteral lit -> do
    node <- Rdf.NodeLiteral <$> encodeLiteral lit
    return [emptyDescription node]
  TermMap m -> do
      triples <- L.concat <$> (CM.mapM (forKeyVal subject) $ M.toList m)
      return [Rdf.Description (resourceToNode subject) $ Rdf.Graph $ S.fromList triples]
    where
      forKeyVal subj (k, v) = do
        -- Note: only string-valued keys are supported
        ks <- Expect.string $ stripTerm k
        node <- nextBlankNode
        descs <- encodeTerm node v
        let pred = keyIri ks
        let objs = subjectsOf descs
        let triples = forObjects subj pred objs
        return $ triples ++ triplesOf descs
  TermWrap (Nominal name inner) -> do
    descs <- encodeTerm subject inner
    return $ (withType name $ L.head descs):(L.tail descs)
  TermOptional mterm -> case mterm of
    Nothing -> pure []
    Just inner -> encodeTerm subject inner
  TermRecord (Record rname fields) -> do
    tripless <- CM.mapM (encodeField rname subject) fields
    return [withType rname $ Rdf.Description (resourceToNode subject) (Rdf.Graph $ S.fromList $ L.concat tripless)]
  TermSet terms -> L.concat <$> CM.mapM encodeEl (S.toList terms)
    where
      encodeEl term = do
        node <- nextBlankNode
        encodeTerm node term
  TermUnion (Injection rname field) -> do
    triples <- encodeField rname subject field
    return [withType rname $ Rdf.Description (resourceToNode subject) (Rdf.Graph $ S.fromList triples)]
  _ -> unexpected "RDF-compatible term" $ show term

encodeType :: Type -> Flow (Graph) Shacl.CommonProperties
encodeType typ = case stripType typ of
    TypeList _ -> any
    TypeLiteral lt -> pure $ encodeLiteralType lt
    TypeMap _ -> any
    TypeWrap name -> any -- TODO: include name
    TypeRecord (RowType rname _ fields) -> do
      props <- CM.zipWithM (encodeFieldType rname) (Just <$> [0..]) fields
      return $ common [Shacl.CommonConstraintProperty $ S.fromList (Shacl.ReferenceDefinition <$> props)]
    TypeSet _ -> any
    TypeUnion (RowType rname _ fields) -> do
        props <- CM.mapM (encodeFieldType rname Nothing) fields
        let shapes = (Shacl.ReferenceAnonymous . toShape) <$> props
        return $ common [Shacl.CommonConstraintXone $ S.fromList shapes]
      where
        toShape prop = node [Shacl.CommonConstraintProperty $ S.fromList [Shacl.ReferenceDefinition prop]]
    _ -> unexpected "type" $ show typ
  where
    -- SHACL's built-in vocabulary is less expressive than Hydra's type system, so for now, SHACL validation simply ends
    -- when inexpressible types are encountered. However, certain constructs such as lists can be validated using
    -- secondary structures. For example, see shsh:ListShape in the SHACL documentation. TODO: explore these constructions.
    any = pure $ common []

node :: [Shacl.CommonConstraint] -> Shacl.Shape
node = Shacl.ShapeNode . Shacl.NodeShape . common

property :: Rdf.Iri -> Shacl.PropertyShape
property iri = Shacl.PropertyShape {
  Shacl.propertyShapeCommon = defaultCommonProperties,
  Shacl.propertyShapeConstraints = S.empty,
  Shacl.propertyShapeDefaultValue = Nothing,
  Shacl.propertyShapeDescription = emptyLangStrings,
  Shacl.propertyShapeName = emptyLangStrings,
  Shacl.propertyShapeOrder = Nothing,
  Shacl.propertyShapePath = iri}

withType :: Name -> Rdf.Description -> Rdf.Description
withType name (Rdf.Description subj (Rdf.Graph triples)) = Rdf.Description subj (Rdf.Graph $ S.insert triple triples)
  where
    subjRes = case subj of
      Rdf.NodeIri iri -> Rdf.ResourceIri iri
      Rdf.NodeBnode bnode -> Rdf.ResourceBnode bnode
    triple = Rdf.Triple subjRes (rdfIri "type") (Rdf.NodeIri $ nameToIri name)
