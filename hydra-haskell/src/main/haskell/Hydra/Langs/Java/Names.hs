module Hydra.Langs.Java.Names where

import Hydra.Kernel

import qualified Hydra.Langs.Java.Syntax as Java


acceptMethodName = "accept" :: String
applyMethodName = "apply" :: String
equalsMethodName = "equals" :: String
getMethodName = "get" :: String
hashCodeMethodName = "hashCode" :: String
instanceName = "instance" :: String
otherInstanceName = "other" :: String
otherwiseMethodName = "otherwise" :: String
partialVisitorName = "PartialVisitor" :: String
setMethodName = "set" :: String
valueName = "value" :: String
visitMethodName = "visit" :: String
visitorName = "Visitor" :: String
visitorReturnParameter = "R" :: String

javaPackageName :: [String] -> Java.PackageName
javaPackageName parts = Java.PackageName (Java.Identifier <$> parts)

hydraCorePackageName :: Maybe Java.PackageName
hydraCorePackageName = Just $ javaPackageName ["hydra", "core"]

javaLangPackageName :: Maybe Java.PackageName
javaLangPackageName = Just $ javaPackageName ["java", "lang"]

javaUtilFunctionPackageName :: Maybe Java.PackageName
javaUtilFunctionPackageName = Just $ javaPackageName ["java", "util", "function"]

javaUtilPackageName :: Maybe Java.PackageName
javaUtilPackageName = Just $ javaPackageName ["java", "util"]
