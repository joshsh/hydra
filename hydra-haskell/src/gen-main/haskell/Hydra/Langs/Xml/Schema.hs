-- | A partial XML Schema model, focusing on datatypes. All simple datatypes (i.e. xsd:anySimpleType and below) are included.
-- | See: https://www.w3.org/TR/xmlschema-2
-- | Note: for most of the XML Schema datatype definitions included here, the associated Hydra type is simply
-- |       the string type. Exceptions are made for xsd:boolean and most of the numeric types, where there is a clearly
-- |       corresponding Hydra literal type.

module Hydra.Langs.Xml.Schema where

import qualified Hydra.Core as Core
import Data.Int
import Data.List as L
import Data.Map as M
import Data.Set as S

newtype AnySimpleType = 
  AnySimpleType {
    unAnySimpleType :: String}
  deriving (Eq, Ord, Read, Show)

_AnySimpleType = (Core.Name "hydra/langs/xml/schema.AnySimpleType")

newtype AnyType = 
  AnyType {
    unAnyType :: String}
  deriving (Eq, Ord, Read, Show)

_AnyType = (Core.Name "hydra/langs/xml/schema.AnyType")

newtype AnyURI = 
  AnyURI {
    unAnyURI :: String}
  deriving (Eq, Ord, Read, Show)

_AnyURI = (Core.Name "hydra/langs/xml/schema.AnyURI")

newtype Base64Binary = 
  Base64Binary {
    unBase64Binary :: String}
  deriving (Eq, Ord, Read, Show)

_Base64Binary = (Core.Name "hydra/langs/xml/schema.Base64Binary")

newtype Boolean = 
  Boolean {
    unBoolean :: Bool}
  deriving (Eq, Ord, Read, Show)

_Boolean = (Core.Name "hydra/langs/xml/schema.Boolean")

newtype Byte = 
  Byte {
    unByte :: Int8}
  deriving (Eq, Ord, Read, Show)

_Byte = (Core.Name "hydra/langs/xml/schema.Byte")

newtype Date = 
  Date {
    unDate :: String}
  deriving (Eq, Ord, Read, Show)

_Date = (Core.Name "hydra/langs/xml/schema.Date")

newtype DateTime = 
  DateTime {
    unDateTime :: String}
  deriving (Eq, Ord, Read, Show)

_DateTime = (Core.Name "hydra/langs/xml/schema.DateTime")

newtype Decimal = 
  Decimal {
    unDecimal :: String}
  deriving (Eq, Ord, Read, Show)

_Decimal = (Core.Name "hydra/langs/xml/schema.Decimal")

newtype Double_ = 
  Double_ {
    unDouble :: Double}
  deriving (Eq, Ord, Read, Show)

_Double = (Core.Name "hydra/langs/xml/schema.Double")

newtype Duration = 
  Duration {
    unDuration :: String}
  deriving (Eq, Ord, Read, Show)

_Duration = (Core.Name "hydra/langs/xml/schema.Duration")

newtype ENTITIES = 
  ENTITIES {
    unENTITIES :: String}
  deriving (Eq, Ord, Read, Show)

_ENTITIES = (Core.Name "hydra/langs/xml/schema.ENTITIES")

newtype ENTITY = 
  ENTITY {
    unENTITY :: String}
  deriving (Eq, Ord, Read, Show)

_ENTITY = (Core.Name "hydra/langs/xml/schema.ENTITY")

newtype Float_ = 
  Float_ {
    unFloat :: Float}
  deriving (Eq, Ord, Read, Show)

_Float = (Core.Name "hydra/langs/xml/schema.Float")

newtype GDay = 
  GDay {
    unGDay :: String}
  deriving (Eq, Ord, Read, Show)

_GDay = (Core.Name "hydra/langs/xml/schema.GDay")

newtype GMonth = 
  GMonth {
    unGMonth :: String}
  deriving (Eq, Ord, Read, Show)

_GMonth = (Core.Name "hydra/langs/xml/schema.GMonth")

newtype GMonthDay = 
  GMonthDay {
    unGMonthDay :: String}
  deriving (Eq, Ord, Read, Show)

_GMonthDay = (Core.Name "hydra/langs/xml/schema.GMonthDay")

newtype GYear = 
  GYear {
    unGYear :: String}
  deriving (Eq, Ord, Read, Show)

_GYear = (Core.Name "hydra/langs/xml/schema.GYear")

newtype GYearMonth = 
  GYearMonth {
    unGYearMonth :: String}
  deriving (Eq, Ord, Read, Show)

_GYearMonth = (Core.Name "hydra/langs/xml/schema.GYearMonth")

newtype HexBinary = 
  HexBinary {
    unHexBinary :: String}
  deriving (Eq, Ord, Read, Show)

_HexBinary = (Core.Name "hydra/langs/xml/schema.HexBinary")

newtype ID = 
  ID {
    unID :: String}
  deriving (Eq, Ord, Read, Show)

_ID = (Core.Name "hydra/langs/xml/schema.ID")

newtype IDREF = 
  IDREF {
    unIDREF :: String}
  deriving (Eq, Ord, Read, Show)

_IDREF = (Core.Name "hydra/langs/xml/schema.IDREF")

newtype IDREFS = 
  IDREFS {
    unIDREFS :: String}
  deriving (Eq, Ord, Read, Show)

_IDREFS = (Core.Name "hydra/langs/xml/schema.IDREFS")

newtype Int_ = 
  Int_ {
    unInt :: Int}
  deriving (Eq, Ord, Read, Show)

_Int = (Core.Name "hydra/langs/xml/schema.Int")

newtype Integer_ = 
  Integer_ {
    unInteger :: Integer}
  deriving (Eq, Ord, Read, Show)

_Integer = (Core.Name "hydra/langs/xml/schema.Integer")

newtype Language = 
  Language {
    unLanguage :: String}
  deriving (Eq, Ord, Read, Show)

_Language = (Core.Name "hydra/langs/xml/schema.Language")

newtype Long = 
  Long {
    unLong :: Int64}
  deriving (Eq, Ord, Read, Show)

_Long = (Core.Name "hydra/langs/xml/schema.Long")

newtype NMTOKEN = 
  NMTOKEN {
    unNMTOKEN :: String}
  deriving (Eq, Ord, Read, Show)

_NMTOKEN = (Core.Name "hydra/langs/xml/schema.NMTOKEN")

newtype NOTATION = 
  NOTATION {
    unNOTATION :: String}
  deriving (Eq, Ord, Read, Show)

_NOTATION = (Core.Name "hydra/langs/xml/schema.NOTATION")

newtype Name = 
  Name {
    unName :: String}
  deriving (Eq, Ord, Read, Show)

_Name = (Core.Name "hydra/langs/xml/schema.Name")

newtype NegativeInteger = 
  NegativeInteger {
    unNegativeInteger :: Integer}
  deriving (Eq, Ord, Read, Show)

_NegativeInteger = (Core.Name "hydra/langs/xml/schema.NegativeInteger")

newtype NonNegativeInteger = 
  NonNegativeInteger {
    unNonNegativeInteger :: Integer}
  deriving (Eq, Ord, Read, Show)

_NonNegativeInteger = (Core.Name "hydra/langs/xml/schema.NonNegativeInteger")

newtype NonPositiveInteger = 
  NonPositiveInteger {
    unNonPositiveInteger :: Integer}
  deriving (Eq, Ord, Read, Show)

_NonPositiveInteger = (Core.Name "hydra/langs/xml/schema.NonPositiveInteger")

newtype NormalizedString = 
  NormalizedString {
    unNormalizedString :: String}
  deriving (Eq, Ord, Read, Show)

_NormalizedString = (Core.Name "hydra/langs/xml/schema.NormalizedString")

newtype PositiveInteger = 
  PositiveInteger {
    unPositiveInteger :: Integer}
  deriving (Eq, Ord, Read, Show)

_PositiveInteger = (Core.Name "hydra/langs/xml/schema.PositiveInteger")

newtype QName = 
  QName {
    unQName :: String}
  deriving (Eq, Ord, Read, Show)

_QName = (Core.Name "hydra/langs/xml/schema.QName")

newtype Short = 
  Short {
    unShort :: Int16}
  deriving (Eq, Ord, Read, Show)

_Short = (Core.Name "hydra/langs/xml/schema.Short")

newtype String_ = 
  String_ {
    unString :: String}
  deriving (Eq, Ord, Read, Show)

_String = (Core.Name "hydra/langs/xml/schema.String")

newtype Time = 
  Time {
    unTime :: String}
  deriving (Eq, Ord, Read, Show)

_Time = (Core.Name "hydra/langs/xml/schema.Time")

newtype Token = 
  Token {
    unToken :: String}
  deriving (Eq, Ord, Read, Show)

_Token = (Core.Name "hydra/langs/xml/schema.Token")

newtype UnsignedByte = 
  UnsignedByte {
    unUnsignedByte :: Int16}
  deriving (Eq, Ord, Read, Show)

_UnsignedByte = (Core.Name "hydra/langs/xml/schema.UnsignedByte")

newtype UnsignedInt = 
  UnsignedInt {
    unUnsignedInt :: Int64}
  deriving (Eq, Ord, Read, Show)

_UnsignedInt = (Core.Name "hydra/langs/xml/schema.UnsignedInt")

newtype UnsignedLong = 
  UnsignedLong {
    unUnsignedLong :: Integer}
  deriving (Eq, Ord, Read, Show)

_UnsignedLong = (Core.Name "hydra/langs/xml/schema.UnsignedLong")

newtype UnsignedShort = 
  UnsignedShort {
    unUnsignedShort :: Int}
  deriving (Eq, Ord, Read, Show)

_UnsignedShort = (Core.Name "hydra/langs/xml/schema.UnsignedShort")

-- | See https://www.w3.org/TR/xmlschema-2/#non-fundamental
data ConstrainingFacet = 
  ConstrainingFacet {}
  deriving (Eq, Ord, Read, Show)

_ConstrainingFacet = (Core.Name "hydra/langs/xml/schema.ConstrainingFacet")

data Datatype = 
  DatatypeAnySimpleType  |
  DatatypeAnyType  |
  DatatypeAnyURI  |
  DatatypeBase64Binary  |
  DatatypeBoolean  |
  DatatypeByte  |
  DatatypeDate  |
  DatatypeDateTime  |
  DatatypeDecimal  |
  DatatypeDouble  |
  DatatypeDuration  |
  DatatypeENTITIES  |
  DatatypeENTITY  |
  DatatypeFloat  |
  DatatypeGDay  |
  DatatypeGMonth  |
  DatatypeGMonthDay  |
  DatatypeGYear  |
  DatatypeGYearMonth  |
  DatatypeHexBinary  |
  DatatypeID  |
  DatatypeIDREF  |
  DatatypeIDREFS  |
  DatatypeInt  |
  DatatypeInteger  |
  DatatypeLanguage  |
  DatatypeLong  |
  DatatypeNMTOKEN  |
  DatatypeNOTATION  |
  DatatypeName  |
  DatatypeNegativeInteger  |
  DatatypeNonNegativeInteger  |
  DatatypeNonPositiveInteger  |
  DatatypeNormalizedString  |
  DatatypePositiveInteger  |
  DatatypeQName  |
  DatatypeShort  |
  DatatypeString  |
  DatatypeTime  |
  DatatypeToken  |
  DatatypeUnsignedByte  |
  DatatypeUnsignedInt  |
  DatatypeUnsignedLong  |
  DatatypeUnsignedShort 
  deriving (Eq, Ord, Read, Show)

_Datatype = (Core.Name "hydra/langs/xml/schema.Datatype")

_Datatype_anySimpleType = (Core.FieldName "anySimpleType")

_Datatype_anyType = (Core.FieldName "anyType")

_Datatype_anyURI = (Core.FieldName "anyURI")

_Datatype_base64Binary = (Core.FieldName "base64Binary")

_Datatype_boolean = (Core.FieldName "boolean")

_Datatype_byte = (Core.FieldName "byte")

_Datatype_date = (Core.FieldName "date")

_Datatype_dateTime = (Core.FieldName "dateTime")

_Datatype_decimal = (Core.FieldName "decimal")

_Datatype_double = (Core.FieldName "double")

_Datatype_duration = (Core.FieldName "duration")

_Datatype_ENTITIES = (Core.FieldName "ENTITIES")

_Datatype_ENTITY = (Core.FieldName "ENTITY")

_Datatype_float = (Core.FieldName "float")

_Datatype_gDay = (Core.FieldName "gDay")

_Datatype_gMonth = (Core.FieldName "gMonth")

_Datatype_gMonthDay = (Core.FieldName "gMonthDay")

_Datatype_gYear = (Core.FieldName "gYear")

_Datatype_gYearMonth = (Core.FieldName "gYearMonth")

_Datatype_hexBinary = (Core.FieldName "hexBinary")

_Datatype_ID = (Core.FieldName "ID")

_Datatype_IDREF = (Core.FieldName "IDREF")

_Datatype_IDREFS = (Core.FieldName "IDREFS")

_Datatype_int = (Core.FieldName "int")

_Datatype_integer = (Core.FieldName "integer")

_Datatype_language = (Core.FieldName "language")

_Datatype_long = (Core.FieldName "long")

_Datatype_NMTOKEN = (Core.FieldName "NMTOKEN")

_Datatype_NOTATION = (Core.FieldName "NOTATION")

_Datatype_name = (Core.FieldName "name")

_Datatype_negativeInteger = (Core.FieldName "negativeInteger")

_Datatype_nonNegativeInteger = (Core.FieldName "nonNegativeInteger")

_Datatype_nonPositiveInteger = (Core.FieldName "nonPositiveInteger")

_Datatype_normalizedString = (Core.FieldName "normalizedString")

_Datatype_positiveInteger = (Core.FieldName "positiveInteger")

_Datatype_qName = (Core.FieldName "qName")

_Datatype_short = (Core.FieldName "short")

_Datatype_string = (Core.FieldName "string")

_Datatype_time = (Core.FieldName "time")

_Datatype_token = (Core.FieldName "token")

_Datatype_unsignedByte = (Core.FieldName "unsignedByte")

_Datatype_unsignedInt = (Core.FieldName "unsignedInt")

_Datatype_unsignedLong = (Core.FieldName "unsignedLong")

_Datatype_unsignedShort = (Core.FieldName "unsignedShort")
