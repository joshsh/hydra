-- | A DSL for building BNF grammars

module Hydra.Dsl.Grammars where

import qualified Hydra.Grammar as G

import Data.String(IsString(..))


instance IsString G.Pattern where fromString = symbol

infixr 0 >:
(>:) :: String -> G.Pattern -> G.Pattern
l >: p = G.PatternLabeled $ G.LabeledPattern (G.Label l) p

alts :: [G.Pattern] -> G.Pattern
alts = G.PatternAlternatives

alts01 :: [G.Pattern] -> G.Pattern
alts01 ps = alts $ [terminal ""] ++ ps

define :: String -> [G.Pattern] -> G.Production
define s pats = G.Production (G.Symbol s) pat
  where
    pat = case pats of
      [p] -> p
      _ -> alts pats

ignored :: G.Pattern -> G.Pattern
ignored = G.PatternIgnored

list :: [G.Pattern] -> G.Pattern
list = G.PatternSequence

nil :: G.Pattern
nil = G.PatternNil

opt :: G.Pattern -> G.Pattern
opt = G.PatternOption

plus :: G.Pattern -> G.Pattern
plus = G.PatternPlus

regex :: String -> G.Pattern
regex = G.PatternRegex . G.Regex

-- | A helper which matches patterns like "foo.bar.quux" or "one; two; three; four"
sep :: G.Pattern -> G.Pattern -> G.Pattern
sep separator pat = list[pat, star(list[separator, pat])]

-- | A helper which matches patterns like "foo.bar.quux" or "foo.bar.quux." (i.e. trailing separators are allowed)
sepp :: G.Pattern -> G.Pattern -> G.Pattern
sepp separator pat = list[pat, star(list[separator, pat]), opt(separator)]

star :: G.Pattern -> G.Pattern
star = G.PatternStar

symbol :: String -> G.Pattern
symbol = G.PatternNonterminal . G.Symbol

terminal :: String -> G.Pattern
terminal = G.PatternConstant . G.Constant
