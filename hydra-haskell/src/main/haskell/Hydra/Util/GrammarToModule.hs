module Hydra.Util.GrammarToModule where

import Hydra.Common
import Hydra.Core
import Hydra.Evaluation
import Hydra.Grammar
import Hydra.Graph
import Hydra.Impl.Haskell.Sources.Core (hydraCoreName)
import Hydra.Impl.Haskell.Dsl.Types as Types
import Hydra.Impl.Haskell.Dsl.Terms as Terms
import Hydra.Impl.Haskell.Dsl.Standard
import Hydra.Util.Formatting
import Hydra.CoreEncoding

import qualified Data.List as L
import qualified Data.Map as M
import qualified Data.Maybe as Y


grammarToModule :: Context Meta -> Grammar -> GraphName -> Module Meta
grammarToModule cx (Grammar prods) gname = Module graph []
  where
    graph = Graph gname els exprs hydraCoreName
      where
        exprs = const True -- TODO: not strictly true; consider removing exprs from Graph

        els = pairToElement <$> L.concat (L.zipWith makeElements (capitalize . fst <$> prodPairs) (snd <$> prodPairs))
          where
            prodPairs = (\(Production (Symbol s) pat) -> (s, pat)) <$> prods
            pairToElement (lname, typ) = Element (toName lname) (Terms.element _Type) (encodeType cx typ)
        
    toName lname = fromQname gname lname
    
    findNames pats = L.reverse $ fst (L.foldl nextName ([], M.empty) pats)
      where
        nextName (names, nameMap) pat = (nn:names, M.insert rn ni nameMap)
          where
            rn = rawName pat
            (nn, ni) = case M.lookup rn nameMap of
              Nothing -> (rn, 1)
              Just i -> (rn ++ show (i+1), i+1)

        rawName pat = case pat of
          PatternNil -> "none"
          PatternLabeled (LabeledPattern (Label l) _) -> l
          PatternConstant _ -> "constant"
          PatternRegex _ -> "regex"
          PatternNonterminal (Symbol s) -> decapitalize s
          PatternSequence _ -> "sequence"
          PatternAlternatives _ -> "alts"
          PatternOption p -> "option" ++ capitalize (rawName p)
          PatternStar p -> "star" ++ capitalize (rawName p)
          PatternPlus p -> "plus" ++ capitalize (rawName p)

    isComplex pat = case pat of
      PatternLabeled (LabeledPattern _ p) -> isComplex p
      PatternSequence _ -> True
      PatternAlternatives _ -> True
      _ -> False
      
    makeElements lname pat = forPat pat
      where
        forPat pat = case pat of
          PatternNil -> [(lname, Types.unit)]
          PatternLabeled (LabeledPattern (Label l) p) -> forPat p
          PatternConstant _ -> []
          PatternRegex _ -> [(lname, Types.string)]
          PatternNonterminal (Symbol other) -> [(lname, Types.nominal $ toName other)]
          PatternSequence pats -> forRecordOrUnion Types.record pats
          PatternAlternatives pats -> forRecordOrUnion Types.union pats
          PatternOption p -> mod "Option" Types.optional p
          PatternStar p -> mod "Elmt" Types.list p
          PatternPlus p -> mod "Elmt" nonemptyList p

        forRecordOrUnion c pats = (lname, c fields):els
            where
              fieldPairs = Y.catMaybes $ L.zipWith toField (findNames pats) pats
              fields = fst <$> fieldPairs
              els = L.concat (snd <$> fieldPairs)
              
        toField n p = case p of
          PatternConstant _ -> Nothing
          _ -> Just $ descend n f2 p
            where
              f2 ((lname, typ):rest) = (FieldType (FieldName n) typ, rest)
              
        mod n f p = descend n f2 p
          where
            f2 ((lname, typ):rest) = (lname, f typ):rest
            
        descend n f p = f $ if isComplex p
            then (lname, Types.nominal (toName $ fst $ L.head cpairs)):cpairs
            else if L.null cpairs
              then [(lname, Types.unit)]
              else (lname, snd (L.head cpairs)):L.tail cpairs
          where
            cpairs = makeElements (childName lname n) p

    childName lname n = lname ++ "." ++ capitalize n
