-- | A DSL of short names for literal types

module Hydra.Dsl.LiteralTypes where

import Hydra.Core


bigfloat :: LiteralType
bigfloat = float FloatTypeBigfloat

bigint :: LiteralType
bigint = LiteralTypeInteger IntegerTypeBigint

binary :: LiteralType
binary = LiteralTypeBinary

boolean :: LiteralType
boolean = LiteralTypeBoolean

float32 :: LiteralType
float32 = float FloatTypeFloat32

float64 :: LiteralType
float64 = float FloatTypeFloat64

float :: FloatType -> LiteralType
float = LiteralTypeFloat

int16 :: LiteralType
int16 = integer IntegerTypeInt16

int32 :: LiteralType
int32 = integer IntegerTypeInt32

int64 :: LiteralType
int64 = integer IntegerTypeInt64

int8 :: LiteralType
int8 = integer IntegerTypeInt8

integer :: IntegerType -> LiteralType
integer = LiteralTypeInteger

string :: LiteralType
string = LiteralTypeString

uint16 :: LiteralType
uint16 = integer IntegerTypeUint16

uint32 :: LiteralType
uint32 = integer IntegerTypeUint32

uint64 :: LiteralType
uint64 = integer IntegerTypeUint64

uint8 :: LiteralType
uint8 = integer IntegerTypeUint8
