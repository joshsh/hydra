-- | A basic Datalog model

module Hydra.Langs.Datalog.Syntax where

import qualified Hydra.Core as Core
import Data.List
import Data.Map
import Data.Set

newtype Constant = 
  Constant {
    unConstant :: String}
  deriving (Eq, Ord, Read, Show)

_Constant = (Core.Name "hydra/langs/datalog/syntax.Constant")

newtype Relation = 
  Relation {
    unRelation :: String}
  deriving (Eq, Ord, Read, Show)

_Relation = (Core.Name "hydra/langs/datalog/syntax.Relation")

newtype Variable = 
  Variable {
    unVariable :: String}
  deriving (Eq, Ord, Read, Show)

_Variable = (Core.Name "hydra/langs/datalog/syntax.Variable")

newtype Program = 
  Program {
    unProgram :: [Program_Elmt]}
  deriving (Eq, Ord, Read, Show)

_Program = (Core.Name "hydra/langs/datalog/syntax.Program")

data Program_Elmt = 
  Program_ElmtFact Fact |
  Program_ElmtRule Rule
  deriving (Eq, Ord, Read, Show)

_Program_Elmt = (Core.Name "hydra/langs/datalog/syntax.Program.Elmt")

_Program_Elmt_fact = (Core.Name "fact")

_Program_Elmt_rule = (Core.Name "rule")

data Fact = 
  Fact {
    factRelation :: Relation,
    factConstantList :: ConstantList}
  deriving (Eq, Ord, Read, Show)

_Fact = (Core.Name "hydra/langs/datalog/syntax.Fact")

_Fact_relation = (Core.Name "relation")

_Fact_constantList = (Core.Name "constantList")

data Rule = 
  Rule {
    ruleAtom :: Atom,
    ruleAtomList :: AtomList}
  deriving (Eq, Ord, Read, Show)

_Rule = (Core.Name "hydra/langs/datalog/syntax.Rule")

_Rule_atom = (Core.Name "atom")

_Rule_atomList = (Core.Name "atomList")

data Atom = 
  Atom {
    atomRelation :: Relation,
    atomTermList :: TermList}
  deriving (Eq, Ord, Read, Show)

_Atom = (Core.Name "hydra/langs/datalog/syntax.Atom")

_Atom_relation = (Core.Name "relation")

_Atom_termList = (Core.Name "termList")

data AtomList = 
  AtomListSingle Atom |
  AtomListMultiple AtomList_Multiple
  deriving (Eq, Ord, Read, Show)

_AtomList = (Core.Name "hydra/langs/datalog/syntax.AtomList")

_AtomList_single = (Core.Name "single")

_AtomList_multiple = (Core.Name "multiple")

data AtomList_Multiple = 
  AtomList_Multiple {
    atomList_MultipleAtom :: Atom,
    atomList_MultipleAtomList :: AtomList}
  deriving (Eq, Ord, Read, Show)

_AtomList_Multiple = (Core.Name "hydra/langs/datalog/syntax.AtomList.Multiple")

_AtomList_Multiple_atom = (Core.Name "atom")

_AtomList_Multiple_atomList = (Core.Name "atomList")

data Term = 
  TermConstant Constant |
  TermVariable Variable
  deriving (Eq, Ord, Read, Show)

_Term = (Core.Name "hydra/langs/datalog/syntax.Term")

_Term_constant = (Core.Name "constant")

_Term_variable = (Core.Name "variable")

data TermList = 
  TermListSingle Term |
  TermListMultiple TermList_Multiple
  deriving (Eq, Ord, Read, Show)

_TermList = (Core.Name "hydra/langs/datalog/syntax.TermList")

_TermList_single = (Core.Name "single")

_TermList_multiple = (Core.Name "multiple")

data TermList_Multiple = 
  TermList_Multiple {
    termList_MultipleTerm :: Term,
    termList_MultipleTermList :: TermList}
  deriving (Eq, Ord, Read, Show)

_TermList_Multiple = (Core.Name "hydra/langs/datalog/syntax.TermList.Multiple")

_TermList_Multiple_term = (Core.Name "term")

_TermList_Multiple_termList = (Core.Name "termList")

data ConstantList = 
  ConstantListSingle Constant |
  ConstantListMultiple ConstantList_Multiple
  deriving (Eq, Ord, Read, Show)

_ConstantList = (Core.Name "hydra/langs/datalog/syntax.ConstantList")

_ConstantList_single = (Core.Name "single")

_ConstantList_multiple = (Core.Name "multiple")

data ConstantList_Multiple = 
  ConstantList_Multiple {
    constantList_MultipleConstant :: Constant,
    constantList_MultipleConstantList :: ConstantList}
  deriving (Eq, Ord, Read, Show)

_ConstantList_Multiple = (Core.Name "hydra/langs/datalog/syntax.ConstantList.Multiple")

_ConstantList_Multiple_constant = (Core.Name "constant")

_ConstantList_Multiple_constantList = (Core.Name "constantList")
