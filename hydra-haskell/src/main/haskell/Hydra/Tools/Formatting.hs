-- | String formatting utilities

module Hydra.Tools.Formatting where

import Hydra.Basics
import qualified Hydra.Lib.Strings as Strings

import qualified Data.Char as C
import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Set as S
import qualified Data.Maybe as Y


data CaseConvention = CaseConventionCamel | CaseConventionPascal | CaseConventionLowerSnake | CaseConventionUpperSnake

convertCase :: CaseConvention -> CaseConvention -> String -> String
convertCase from to original = case to of
    CaseConventionCamel -> decapitalize $ L.concat (capitalize . Strings.toLower <$> parts)
    CaseConventionPascal -> L.concat (capitalize . Strings.toLower <$> parts)
    CaseConventionLowerSnake -> L.intercalate "_" (Strings.toLower <$> parts)
    CaseConventionUpperSnake -> L.intercalate "_" (Strings.toUpper <$> parts)
  where
    parts = case from of
      CaseConventionCamel -> byCaps
      CaseConventionPascal -> byCaps
      CaseConventionLowerSnake -> byUnderscores
      CaseConventionUpperSnake -> byUnderscores
    byUnderscores = Strings.splitOn "_" original
    byCaps = L.foldl helper [""] $ L.reverse $ decapitalize original
      where
        helper (h:r) c = ["" | C.isUpper c] ++ ((c:h):r)

convertCaseCamelToLowerSnake :: String -> String
convertCaseCamelToLowerSnake = convertCase CaseConventionCamel CaseConventionLowerSnake

convertCaseCamelToUpperSnake :: String -> String
convertCaseCamelToUpperSnake = convertCase CaseConventionCamel CaseConventionUpperSnake

convertCasePascalToUpperSnake :: String -> String
convertCasePascalToUpperSnake = convertCase CaseConventionPascal CaseConventionUpperSnake

escapeWithUnderscore :: S.Set String -> String -> String
escapeWithUnderscore reserved s = if S.member s reserved then s ++ "_" else s

indentLines :: String -> String
indentLines s = unlines (indent <$> lines s)
  where
    indent l = "    " ++ l

javaStyleComment :: String -> String
javaStyleComment s = "/**\n" ++ " * " ++ s ++ "\n */"

nonAlnumToUnderscores :: String -> String
nonAlnumToUnderscores = L.reverse . fst . L.foldl replace ([], False)
  where
    replace (s, b) c = if isAlnum c
      then (c:s, False)
      else if b
        then (s, True)
        else ('_':s, True)
    isAlnum c = (c >= 'A' && c <= 'Z')
      || (c >= 'a' && c <= 'z')
      || (c >= '0' && c <= '9')

sanitizeWithUnderscores :: S.Set String -> String -> String
sanitizeWithUnderscores reserved = escapeWithUnderscore reserved . nonAlnumToUnderscores

stripLeadingAndTrailingWhitespace :: String -> String
stripLeadingAndTrailingWhitespace s = L.dropWhile C.isSpace $ L.reverse $ L.dropWhile C.isSpace $ L.reverse s

toLowerCase :: String -> String
toLowerCase = fmap C.toLower

toUpperCase :: String -> String
toUpperCase = fmap C.toUpper

withCharacterAliases :: String -> String
withCharacterAliases original = L.filter C.isAlphaNum $ L.concat $ alias <$> original
  where
    alias c = Y.maybe [c] capitalize $ M.lookup (C.ord c) aliases

    -- Taken from: https://cs.stanford.edu/people/miles/iso8859.html
    aliases = M.fromList [
      (32, "sp"),
      (33, "excl"),
      (34, "quot"),
      (35, "num"),
      (36, "dollar"),
      (37, "percnt"),
      (38, "amp"),
      (39, "apos"),
      (40, "lpar"),
      (41, "rpar"),
      (42, "ast"),
      (43, "plus"),
      (44, "comma"),
      (45, "minus"),
      (46, "period"),
      (47, "sol"),
      (58, "colon"),
      (59, "semi"),
      (60, "lt"),
      (61, "equals"),
      (62, "gt"),
      (63, "quest"),
      (64, "commat"),
      (91, "lsqb"),
      (92, "bsol"),
      (93, "rsqb"),
      (94, "circ"),
      (95, "lowbar"),
      (96, "grave"),
      (123, "lcub"),
      (124, "verbar"),
      (125, "rcub"),
      (126, "tilde")]

-- A simple soft line wrap which is suitable for code comments
wrapLine :: Int -> String -> String
wrapLine maxlen = L.intercalate "\n" . helper []
  where
    helper prev rem = if L.length rem <= maxlen
        then L.reverse (rem:prev)
        else if L.null prefix
        then helper (trunc:prev) $ L.drop maxlen rem
        else helper ((init prefix):prev) $ suffix ++ L.drop maxlen rem
      where
        trunc = L.take maxlen rem
        (prefix, suffix) = case span (\c -> c /= ' ' && c /= '\t') (reverse trunc) of
                                      (restRev, firstRev) -> (reverse firstRev, reverse restRev)
