{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Protobuf.Proto3 where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


proto3Ns = Namespace "hydra/langs/protobuf/proto3"
proto3 = typeref proto3Ns

proto3Module :: Module
proto3Module = Module proto3Ns elements [hydraCoreModule] $
    Just ("A model for Protocol Buffers v3 enum and message types, designed as a target for transformations."
      ++ "This model is loosely based on https://github.com/protocolbuffers/protobuf/blob/main/src/google/protobuf/type.proto,"
      ++ " as well as the proto3 reference documentation")
  where
    def = datatype proto3Ns
    elements = [

      def "Definition" $
        union [
          "enum">: proto3 "EnumDefinition",
          "message">: proto3 "MessageDefinition"],

      def "EnumDefinition" $
        doc "Enum type definition" $
        record [
          "name">:
            doc "Enum type name" $
            proto3 "TypeName",
          "values">:
            doc "Enum value definitions" $
            list $ proto3 "EnumValue",
          "options">:
            doc "Protocol buffer options" $
            list $ proto3 "Option"],

      def "EnumValue" $
        doc "Enum value definition" $
        record [
          "name">:
            doc "Enum value name" $
            proto3 "EnumValueName",
          "number">:
            doc "Enum value number"
            int32,
          "options">:
            doc "Protocol buffer options" $
            list $ proto3 "Option"],

      def "EnumValueName" string,

      def "Field" $
        doc "A single field of a message type" $
        record [
          "name">:
            doc "The field name" $
            proto3 "FieldName",
          "jsonName">:
            doc "The field JSON name" $
            optional string,
          "type">:
            doc "The datatype of the field" $
            proto3 "FieldType",
          "number">:
            doc "The field number"
            int32,
          "options">:
            doc "The protocol buffer options" $
            list $ proto3 "Option"],

      def "FieldName" $
        doc "The name of a field"
        string,

      def "FieldType" $
        union [
          "map">: proto3 "SimpleType",
          "oneof">: list $ proto3 "Field",
          "repeated">: proto3 "SimpleType",
          "simple">: proto3 "SimpleType"],

      def "FileReference" string,

      def "MessageDefinition" $
        doc "A protocol buffer message type" $
        record [
          "name">:
            doc "The fully qualified message name" $
            proto3 "TypeName",
          "fields">:
            doc "The list of fields" $
            list $ proto3 "Field",
          "options">:
            doc "The protocol buffer options" $
            list $ proto3 "Option"],

      def "Option" $
        doc ("A protocol buffer option, which can be attached to a message, field, " ++
             "enumeration, etc") $
        record [
          "name">:
            doc ("The option's name. For protobuf built-in options (options defined in " ++
                 "descriptor.proto), this is the short name. For example, `\"map_entry\"`. " ++
                 "For custom options, it should be the fully-qualified name. For example, " ++
                 "`\"google.api.http\"`.")
            string,
          "value">:
            doc ("The option's value") $
            string], -- TODO: although "Any" may be overkill, we do need to accommodate option values other than strings

      def "PackageName" string,

      def "ProtoFile" $
        doc "A .proto file, usually containing one or more enum or message type definitions" $
        record [
          "package">: proto3 "PackageName",
          "imports">: list $ proto3 "FileReference",
          "types">: list $ proto3 "Definition",
          "options">: list $ proto3 "Option"],

      def "ScalarType" $
        doc "One of several Proto3 scalar types" $
        enum [
          "bool",
          "bytes",
          "double",
          "fixed32",
          "fixed64",
          "float",
          "int32",
          "int64",
          "sfixed32",
          "sfixed64",
          "sint32",
          "sint64",
          "string",
          "uint32",
          "uint64"],

      def "SimpleType" $
        doc "A scalar type or a reference to an enum type or message type" $
        union [
          "reference">: proto3 "TypeName",
          "scalar">: proto3 "ScalarType"],

      def "TypeName" $
        doc "The local name of an enum type or message type"
        string,

      def "TypeReference" $
        doc "A reference to an enum type or message type"
        string]
