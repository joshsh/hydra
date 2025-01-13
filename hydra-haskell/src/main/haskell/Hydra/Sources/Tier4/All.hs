module Hydra.Sources.Tier4.All(
  module Hydra.Sources.Tier4.All,
  module Hydra.Sources.Tier3.All,
  -- Note: individual Tier-4 modules are not exported, as they are currently not guaranteed to be free of name collisions
) where

import Hydra.Sources.Tier3.All
import Hydra.Sources.Tier4.Ext.Avro.Schema
import Hydra.Sources.Tier4.Ext.Csharp.Language
import Hydra.Sources.Tier4.Ext.Csharp.Syntax
import Hydra.Sources.Tier4.Ext.Cypher.Features
import Hydra.Sources.Tier4.Ext.Cypher.OpenCypher
import Hydra.Sources.Tier4.Ext.Gql.OpenGql
import Hydra.Sources.Tier4.Ext.Graphql.Syntax
import Hydra.Sources.Tier4.Ext.Haskell.Ast
import Hydra.Sources.Tier4.Ext.Java.Language
import Hydra.Sources.Tier4.Ext.Java.Syntax
import Hydra.Sources.Tier4.Ext.Json.Decoding
import Hydra.Sources.Tier4.Ext.Json.Schema
import Hydra.Sources.Tier4.Ext.Pegasus.Pdl
import Hydra.Sources.Tier4.Ext.Protobuf.Any
import Hydra.Sources.Tier4.Ext.Protobuf.Language
import Hydra.Sources.Tier4.Ext.Protobuf.Proto3
import Hydra.Sources.Tier4.Ext.Protobuf.SourceContext
import Hydra.Sources.Tier4.Ext.Python.Language
import Hydra.Sources.Tier4.Ext.Python.Syntax
import Hydra.Sources.Tier4.Ext.Rdf.Syntax
import Hydra.Sources.Tier4.Ext.RelationalModel
import Hydra.Sources.Tier4.Ext.Scala.Meta
import Hydra.Sources.Tier4.Ext.Shacl.Model
import Hydra.Sources.Tier4.Ext.Tabular
import Hydra.Sources.Tier4.Ext.Yaml.Model
import Hydra.Sources.Tier4.Test.TestSuite
import Hydra.Sources.Tier4.Ext.Pg.Mapping
import Hydra.Sources.Tier4.Ext.Pg.Model
import Hydra.Sources.Tier4.Ext.Pg.Query
import Hydra.Sources.Tier4.Ext.Pg.Validation


allModules :: [Module]
allModules = mainModules ++ testModules

mainModules :: [Module]
mainModules = kernelModules ++ tier4LangModules

testModules :: [Module]
testModules = [
  testSuiteModule]

tier4LangModules :: [Module]
tier4LangModules = [
  avroSchemaModule,
  csharpLanguageModule,
  csharpSyntaxModule,
  graphqlSyntaxModule,
  haskellAstModule,
  javaLanguageModule,
  javaSyntaxModule,
  jsonDecodingModule,
  jsonSchemaModule,
  openCypherModule,
  openCypherFeaturesModule,
  openGqlModule,
  pegasusPdlModule,
  proto3Module,
  protobufAnyModule,
  protobufLanguageModule,
  protobufSourceContextModule,
  pythonLanguageModule,
  pythonSyntaxModule,
  rdfSyntaxModule,
  relationalModelModule,
  scalaMetaModule,
  shaclModelModule,
  tabularModule,
  pgMappingModule,
  pgModelModule,
  pgQueryModule,
  pgValidationModule,
  yamlModelModule]
