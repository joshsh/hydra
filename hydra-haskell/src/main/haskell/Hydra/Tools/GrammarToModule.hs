-- | A utility for converting a BNF grammar to a Hydra module

module Hydra.Tools.GrammarToModule where

import Hydra.Kernel
import Hydra.Dsl.Annotations
import Hydra.Dsl.Bootstrap as Bootstrap
import Hydra.Dsl.Types as Types
import Hydra.Dsl.Terms as Terms
import qualified Hydra.Grammar as G

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y


grammarToModule :: Namespace -> G.Grammar -> Maybe String -> Module
grammarToModule ns (G.Grammar prods) desc = Module ns elements [] desc
  where
    elements = pairToElement <$> L.concat (L.zipWith (makeElements False) (capitalize . fst <$> prodPairs) (snd <$> prodPairs))
      where
        prodPairs = (\(G.Production (G.Symbol s) pat) -> (s, pat)) <$> prods
        pairToElement (lname, typ) = Bootstrap.typeDefinitionElement (toName lname) typ

    toName local = unqualifyName $ QualifiedName (Just ns) local

    findNames pats = L.reverse $ fst (L.foldl nextName ([], M.empty) pats)
      where
        nextName (names, nameMap) pat = (nn:names, M.insert rn ni nameMap)
          where
            rn = rawName pat
            (nn, ni) = case M.lookup rn nameMap of
              Nothing -> (rn, 1)
              Just i -> (rn ++ show (i+1), i+1)

        rawName pat = case pat of
          G.PatternNil -> "none"
          G.PatternIgnored _ -> "ignored"
          G.PatternLabeled (G.LabeledPattern (G.Label l) _) -> l
          G.PatternConstant (G.Constant c) -> decapitalize $ withCharacterAliases c
          G.PatternRegex _ -> "regex"
          G.PatternNonterminal (G.Symbol s) -> decapitalize s
          G.PatternSequence _ -> "sequence"
          G.PatternAlternatives _ -> "alts"
          G.PatternOption p -> decapitalize (rawName p)
          G.PatternStar p -> "listOf" ++ capitalize (rawName p)
          G.PatternPlus p -> "listOf" ++ capitalize (rawName p)

    isComplex pat = case pat of
      G.PatternLabeled (G.LabeledPattern _ p) -> isComplex p
      G.PatternSequence pats -> isNontrivial True pats
      G.PatternAlternatives pats -> isNontrivial False pats
      _ -> False

    isNontrivial isRecord pats = if L.length minPats == 1
        then case L.head minPats of
          G.PatternLabeled _ -> True
          _ -> False
        else True
      where
        minPats = simplify isRecord pats

    -- Remove trivial patterns from records
    simplify isRecord pats = if isRecord then L.filter (not . isConstant) pats else pats
      where
        isConstant p = case p of
          G.PatternConstant _ -> True
          _ -> False

    makeElements omitTrivial lname pat = forPat pat
      where
        forPat pat = case pat of
          G.PatternNil -> trivial
          G.PatternIgnored _ -> []
          G.PatternLabeled (G.LabeledPattern (G.Label l) p) -> forPat p
          G.PatternConstant _ -> trivial
          G.PatternRegex _ -> [(lname, Types.string)]
          G.PatternNonterminal (G.Symbol other) -> [(lname, TypeVariable $ toName other)]
          G.PatternSequence pats -> forRecordOrUnion True Types.record pats
          G.PatternAlternatives pats -> forRecordOrUnion False Types.union pats
          G.PatternOption p -> mod "Option" Types.optional p
          G.PatternStar p -> mod "Elmt" Types.list p
          G.PatternPlus p -> mod "Elmt" nonemptyList p

        trivial = if omitTrivial then [] else [(lname, Types.unit)]

        forRecordOrUnion isRecord construct pats = if isNontrivial isRecord pats
            then (lname, construct fields):els
            -- Eliminate single-field record and union types, unless the field has a user-defined name
            else forPat $ L.head minPats
          where
            fieldPairs = L.zipWith toField (findNames minPats) minPats
            fields = fst <$> fieldPairs
            els = L.concat (snd <$> fieldPairs)
            minPats = simplify isRecord pats

        toField n p = descend n f2 p
          where
            f2 ((lname, typ):rest) = (FieldType (Name n) typ, rest)

        mod n f p = descend n f2 p
          where
            f2 ((lname, typ):rest) = (lname, f typ):rest

        descend n f p = f $ if isComplex p
            then (lname, TypeVariable (toName $ fst $ L.head cpairs)):cpairs
            else if L.null cpairs
              then [(lname, Types.unit)]
              else (lname, snd (L.head cpairs)):L.tail cpairs
          where
            cpairs = makeElements False (childName lname n) p

    childName lname n = lname ++ "." ++ capitalize n
