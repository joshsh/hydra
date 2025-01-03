{-# LANGUAGE OverloadedStrings #-}

module Hydra.Sources.Tier4.Ext.Java.Language where

import Hydra.Sources.Tier3.All
import Hydra.Dsl.Base as Base
import Hydra.Dsl.Coders as Coders
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


javaLanguageDefinition :: String -> TTerm a -> TElement a
javaLanguageDefinition = definitionInModule javaLanguageModule

javaLanguageModule :: Module
javaLanguageModule = Module ns elements [hydraCodersModule, hydraBasicsModule] tier0Modules $
    Just "Language constraints and reserved words for Java"
  where
    ns = Namespace "hydra/ext/java/language"
    elements = [
      el javaMaxTupleLengthDef,
      el javaLanguageDef,
      el reservedWordsDef]

javaMaxTupleLengthDef :: TElement Int
javaMaxTupleLengthDef = javaLanguageDefinition "javaMaxTupleLength" $
  doc ("The maximum supported length of a tuple in Hydra-Java. "
    <> "Note: if this constant is changed, also change Tuples.java correspondingly") $
  int32 9

javaLanguageDef :: TElement (Language)
javaLanguageDef = javaLanguageDefinition "javaLanguage" $
    doc "Language constraints for Java" $
    typed languageT $
    Coders.language "hydra/ext/java"
      eliminationVariants
      literalVariants
      floatTypes
      functionVariants
      integerTypes
      termVariants
      typeVariants
      typePredicate
  where
      eliminationVariants = [
        EliminationVariantList,
        EliminationVariantOptional,
        EliminationVariantProduct,
        EliminationVariantRecord,
        EliminationVariantUnion,
        EliminationVariantWrap]
      literalVariants = [
        LiteralVariantBoolean, -- boolean
        LiteralVariantFloat, -- (see float types)
        LiteralVariantInteger, -- (see integer types)
        LiteralVariantString] -- string
      floatTypes = [
        -- Bigfloat (e.g. as Java's BigDecimal) is excluded for now
        FloatTypeFloat32, -- float
        FloatTypeFloat64] -- double
      functionVariants = [
        FunctionVariantElimination,
        FunctionVariantLambda,
        FunctionVariantPrimitive]
      integerTypes = [
        IntegerTypeBigint, -- BigInteger
        IntegerTypeInt8, -- byte (signed, 8-bit)
        IntegerTypeInt16, -- short (signed, 16-bit)
        IntegerTypeInt32, -- int (signed, 32-bit)
        IntegerTypeInt64, -- long (signed, 64-bit)
        IntegerTypeUint16] -- char (unsigned, 16-bit)
      termVariants = [
        TermVariantApplication,
        TermVariantFunction,
        TermVariantLet,
        TermVariantList,
        TermVariantLiteral,
        TermVariantMap,
        TermVariantOptional,
        TermVariantProduct,
        TermVariantRecord,
        TermVariantSet,
        TermVariantUnion,
        TermVariantVariable,
        TermVariantWrap]
      typeVariants = [
        TypeVariantAnnotated,
        TypeVariantApplication,
        TypeVariantFunction,
        TypeVariantLambda,
        TypeVariantList,
        TypeVariantLiteral,
        TypeVariantMap,
        TypeVariantOptional,
        TypeVariantProduct,
        TypeVariantRecord,
        TypeVariantSet,
        TypeVariantUnion,
        TypeVariantVariable,
        TypeVariantWrap]
      typePredicate = match _Type (Just true) [
        _Type_product>>: lambda "types" $ Equality.ltInt32 @@ (Lists.length @@ var "types") @@ (ref javaMaxTupleLengthDef)]

reservedWordsDef :: TElement (S.Set String)
reservedWordsDef = javaLanguageDefinition "reservedWords" $
  doc "A set of reserved words in Java" $
  typed (setT stringT) $
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
