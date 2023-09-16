{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Langs.Java.Language where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Base as Base
import Hydra.Dsl.Lib.Equality as Equality
import Hydra.Dsl.Lib.Flows as Flows
import Hydra.Dsl.Lib.Lists as Lists
import Hydra.Dsl.Lib.Logic as Logic
import Hydra.Dsl.Lib.Maps as Maps
import Hydra.Dsl.Lib.Sets as Sets
import Hydra.Dsl.Lib.Strings as Strings
import qualified Hydra.Dsl.Terms as Terms
import qualified Hydra.Dsl.Types as Types

import qualified Data.Set as S


javaLanguageDefinition :: String -> Datum a -> Definition a
javaLanguageDefinition = definitionInModule javaLanguageModule

javaLanguageModule :: Module
javaLanguageModule = Module ns elements [hydraCodersModule, hydraBasicsModule] Nothing
  where
    ns = Namespace "hydra/langs/java/language"
    elements = [
      el javaMaxTupleLengthDef,
      el javaLanguageDef,
      el reservedWordsDef
      ]

javaMaxTupleLengthDef :: Definition Int
javaMaxTupleLengthDef = javaLanguageDefinition "javaMaxTupleLength" $
  doc ("The maximum supported length of a tuple in Hydra-Java. "
    <> "Note: if this constant is changed, also change Tuples.java correspondingly") $
  int32 9

javaLanguageDef :: Definition (Language)
javaLanguageDef = javaLanguageDefinition "javaLanguage" $
  doc "Language constraints for Java" $
  typed (Types.apply (TypeVariable _Language) (Types.var "a")) $
  record _Language [
    _Language_name>>: wrap _LanguageName "hydra/langs/java",
    _Language_constraints>>: record _LanguageConstraints [
      _LanguageConstraints_eliminationVariants>>: Sets.fromList @@ ref eliminationVariantsDef,
      _LanguageConstraints_literalVariants>>: Sets.fromList @@ list (unitVariant _LiteralVariant <$> [
        _LiteralVariant_boolean, -- boolean
        _LiteralVariant_float, -- (see float types)
        _LiteralVariant_integer, -- (see integer types)
        _LiteralVariant_string]), -- string
      _LanguageConstraints_floatTypes>>: Sets.fromList @@ list (unitVariant _FloatType <$> [
         -- Bigfloat (e.g. as Java's BigDecimal) is excluded for now
        _FloatType_float32, -- float
        _FloatType_float64]), -- double
      _LanguageConstraints_functionVariants>>: Sets.fromList @@ ref functionVariantsDef,
      _LanguageConstraints_integerTypes>>: Sets.fromList @@ list (unitVariant _IntegerType <$> [
        _IntegerType_bigint, -- BigInteger
        _IntegerType_int16, -- short
        _IntegerType_int32, -- int
        _IntegerType_int64, -- long
        _IntegerType_uint8, -- byte
        _IntegerType_uint16]), -- char
      _LanguageConstraints_termVariants>>: Sets.fromList @@ list (unitVariant _TermVariant <$> [
        _TermVariant_application,
        _TermVariant_function,
        _TermVariant_let,
        _TermVariant_list,
        _TermVariant_literal,
        _TermVariant_map,
        _TermVariant_optional,
        _TermVariant_product,
        _TermVariant_record,
        _TermVariant_set,
        _TermVariant_union,
        _TermVariant_variable,
        _TermVariant_wrap]),
      _LanguageConstraints_typeVariants>>: Sets.fromList @@ list (unitVariant _TypeVariant <$> [
        _TypeVariant_annotated,
        _TypeVariant_application,
        _TypeVariant_function,
        _TypeVariant_lambda,
        _TypeVariant_list,
        _TypeVariant_literal,
        _TypeVariant_map,
        _TypeVariant_optional,
        _TypeVariant_product,
        _TypeVariant_record,
        _TypeVariant_set,
        _TypeVariant_union,
        _TypeVariant_variable,
        _TypeVariant_wrap]),
      _LanguageConstraints_types>>: match _Type (Just true) [
        _Type_product>>: lambda "types" $ Equality.ltInt32 @@ (Lists.length @@ var "types") @@ (ref javaMaxTupleLengthDef)
      ]]]

reservedWordsDef :: Definition (S.Set String)
reservedWordsDef = javaLanguageDefinition "reservedWords" $
  doc "A set of reserved words in Java" $
  (Sets.fromList @@ (Lists.concat @@ list [var "specialNames", var "classNames", var "keywords", var "literals"]))
  `with` [
    "specialNames">:
      doc "Special names reserved for use by Hydra" $
      list ["Elements"],

    "classNames">:
      doc ("java.lang classes as of JDK 7\n"
        <> "See: https://docs.oracle.com/javase/7/docs/api/java/lang/package-summary.html") $
      list [
        "AbstractMethodError", "Appendable", "ArithmeticException", "ArrayIndexOutOfBoundsException",
        "ArrayStoreException", "AssertionError", "AutoCloseable", "Boolean", "BootstrapMethodError", "Byte",
        "CharSequence", "Character", "Class", "ClassCastException", "ClassCircularityError", "ClassFormatError",
        "ClassLoader", "ClassNotFoundException", "ClassValue", "CloneNotSupportedException", "Cloneable", "Comparable",
        "Compiler", "Deprecated", "Double", "Enum", "EnumConstantNotPresentException", "Error", "Exception",
        "ExceptionInInitializerError", "Float", "IllegalAccessError", "IllegalAccessException",
        "IllegalArgumentException", "IllegalMonitorStateException", "IllegalStateException",
        "IllegalThreadStateException", "IncompatibleClassChangeError", "IndexOutOfBoundsException",
        "InheritableThreadLocal", "InstantiationError", "InstantiationException", "Integer", "InternalError",
        "InterruptedException", "Iterable", "LinkageError", "Long", "Math", "NegativeArraySizeException",
        "NoClassDefFoundError", "NoSuchFieldError", "NoSuchFieldException", "NoSuchMethodError", "NoSuchMethodException",
        "NullPointerException", "Number", "NumberFormatException", "Object", "OutOfMemoryError", "Override", "Package",
        "Process", "ProcessBuilder", "Readable", "ReflectiveOperationException", "Runnable", "Runtime",
        "RuntimeException", "RuntimePermission", "SafeVarargs", "SecurityException", "SecurityManager", "Short",
        "StackOverflowError", "StackTraceElement", "StrictMath", "String", "StringBuffer", "StringBuilder",
        "StringIndexOutOfBoundsException", "SuppressWarnings", "System", "Thread", "ThreadDeath",
        "ThreadGroup", "ThreadLocal", "Throwable", "TypeNotPresentException",
        "UnknownError", "UnsatisfiedLinkError", "UnsupportedClassVersionError",
        "UnsupportedOperationException", "VerifyError", "VirtualMachineError", "Void"],

    "keywords">:
      doc ("Keywords and literals are taken from Oracle's Java Tutorials on 2022-05-27; said to be complete for Java 1.8 only\n"
          <> "See: https://docs.oracle.com/javase/tutorial/java/nutsandbolts/_keywords.html") $
      list [
        "abstract", "assert", "boolean", "break", "byte", "case", "catch", "char", "class", "const", "continue",
        "default", "do", "double", "else", "enum", "extends", "final", "finally", "float", "for", "goto", "if",
        "implements", "import", "instanceof", "int", "interface", "long", "native", "new", "package", "private",
        "protected", "public", "return", "short", "static", "strictfp", "super", "switch", "synchronized", "this",
        "throw", "throws", "transient", "try", "void", "volatile", "while"],

    "literals">:
      list ["false", "null", "true"]]
