module Hydra.Sources.Tier4.Langs.Xml.Schema where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap
import Hydra.Dsl.Types as Types


xmlSchemaModule :: Module
xmlSchemaModule = Module ns elements [] $
    Just ("A partial XML Schema model, focusing on datatypes. All simple datatypes (i.e. xsd:anySimpleType and below) are included.\n" ++
      "See: https://www.w3.org/TR/xmlschema-2\n" ++
      "Note: for most of the XML Schema datatype definitions included here, the associated Hydra type is simply\n" ++
      "      the string type. Exceptions are made for xsd:boolean and most of the numeric types, where there is a clearly\n" ++
      "      corresponding Hydra literal type.")
  where
    ns = Namespace "hydra/langs/xml/schema"
    def = datatype ns

    elements = datatypes ++ others

    datatypes = [
      def "AnySimpleType" string,
      def "AnyType" string,
      def "AnyURI" string,
      def "Base64Binary" string,
      def "Boolean" boolean,
      def "Byte" int8,
      def "Date" string,
      def "DateTime" string,
      def "Decimal" string,
      def "Double" float64,
      def "Duration" string,
      def "ENTITIES" string,
      def "ENTITY" string,
      def "Float" float32,
      def "GDay" string,
      def "GMonth" string,
      def "GMonthDay" string,
      def "GYear" string,
      def "GYearMonth" string,
      def "HexBinary" string,
      def "ID" string,
      def "IDREF" string,
      def "IDREFS" string,
      def "Int" int32,
      def "Integer" bigint,
      def "Language" string,
      def "Long" int64,
      def "NMTOKEN" string,
      def "NOTATION" string,
      def "Name" string,
      def "NegativeInteger" bigint,
      def "NonNegativeInteger" bigint,
      def "NonPositiveInteger" bigint,
      def "NormalizedString" string,
      def "PositiveInteger" bigint,
      def "QName" string,
      def "Short" int16,
      def "String" string,
      def "Time" string,
      def "Token" string,
      def "UnsignedByte" uint8,
      def "UnsignedInt" uint32,
      def "UnsignedLong" uint64,
      def "UnsignedShort" uint16]

    others = [
      def "ConstrainingFacet" $
        see "https://www.w3.org/TR/xmlschema-2/#non-fundamental" $
        unit, -- TODO: concrete facets

      def "Datatype" $ enum [
        "anySimpleType",
        "anyType",
        "anyURI",
        "base64Binary",
        "boolean",
        "byte",
        "date",
        "dateTime",
        "decimal",
        "double",
        "duration",
        "ENTITIES",
        "ENTITY",
        "float",
        "gDay",
        "gMonth",
        "gMonthDay",
        "gYear",
        "gYearMonth",
        "hexBinary",
        "ID",
        "IDREF",
        "IDREFS",
        "int",
        "integer",
        "language",
        "long",
        "NMTOKEN",
        "NOTATION",
        "name",
        "negativeInteger",
        "nonNegativeInteger",
        "nonPositiveInteger",
        "normalizedString",
        "positiveInteger",
        "qName",
        "short",
        "string",
        "time",
        "token",
        "unsignedByte",
        "unsignedInt",
        "unsignedLong",
        "unsignedShort"]]
