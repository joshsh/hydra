module Hydra.Sources.Tier4.All(
  module Hydra.Sources.Tier4.All,
  module Hydra.Sources.Tier3.All,
  -- Note: individual Tier-4 modules are not exported, as they are currently not guaranteed to be free of name collisions
) where

import Hydra.Sources.Tier3.All
import Hydra.Sources.Tier4.Langs.Avro.Schema
import Hydra.Sources.Tier4.Langs.Graphql.Syntax
import Hydra.Sources.Tier4.Langs.Haskell.Ast
import Hydra.Sources.Tier4.Langs.Java.Language
import Hydra.Sources.Tier4.Langs.Java.Syntax
import Hydra.Sources.Tier4.Langs.Owl.Syntax
import Hydra.Sources.Tier4.Langs.Parquet.Format
import Hydra.Sources.Tier4.Langs.Pegasus.Pdl
import Hydra.Sources.Tier4.Langs.Protobuf.Any
import Hydra.Sources.Tier4.Langs.Protobuf.Language
import Hydra.Sources.Tier4.Langs.Protobuf.Proto3
import Hydra.Sources.Tier4.Langs.Protobuf.SourceContext
import Hydra.Sources.Tier4.Langs.Rdf.Syntax
import Hydra.Sources.Tier4.Langs.RelationalModel
import Hydra.Sources.Tier4.Langs.Scala.Meta
import Hydra.Sources.Tier4.Langs.Shacl.Model
import Hydra.Sources.Tier4.Langs.Shex.Syntax
import Hydra.Sources.Tier4.Langs.Sql.Ansi
import Hydra.Sources.Tier4.Langs.Tabular
import Hydra.Sources.Tier4.Langs.Tinkerpop.Features
import Hydra.Sources.Tier4.Langs.Tinkerpop.Mappings
import Hydra.Sources.Tier4.Langs.Tinkerpop.PropertyGraph
import Hydra.Sources.Tier4.Langs.Xml.Schema
import Hydra.Sources.Tier4.Langs.Yaml.Model
import Hydra.Sources.Tier4.Test.TestSuite


mainModules :: [Module Kv]
mainModules = kernelModules ++ tier4LangModules

testModules :: [Module Kv]
testModules = [
  testSuiteModule]

tier4LangModules :: [Module Kv]
tier4LangModules = [
  avroSchemaModule,
  graphqlSyntaxModule,
  haskellAstModule,
  javaLanguageModule,
  javaSyntaxModule,
  owlSyntaxModule,
  parquetFormatModule,
  pegasusPdlModule,
  proto3Module,
  protobufAnyModule,
  protobufLanguageModule,
  protobufSourceContextModule,
  rdfSyntaxModule,
  relationalModelModule,
  scalaMetaModule,
  shaclModelModule,
  shexSyntaxModule,
  sqlModule,
  tabularModule,
  tinkerpopFeaturesModule,
  tinkerpopMappingsModule,
  tinkerpopPropertyGraphModule,
  xmlSchemaModule,
  yamlModelModule]

tier4Modules :: [Module Kv]
tier4Modules = tier4LangModules
