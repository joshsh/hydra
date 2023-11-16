{-# LANGUAGE OverloadedStrings #-}

module Hydra.Models.Datalog where

import Hydra.Sources.Tier4.All
import Hydra.Dsl.Grammars
import Hydra.Tools.GrammarToModule
import qualified Hydra.Grammar as G


comma = terminal ","
entail = terminal ":-"
lparen = terminal "("
period = terminal "."
rparen = terminal ")"

datalogSyntaxModule :: Module
datalogSyntaxModule = grammarToModule ns datalogGrammar $
    Just "A basic Datalog model"
  where
    ns = Namespace "hydra/langs/datalog/syntax"

datalogGrammar :: G.Grammar
datalogGrammar = G.Grammar [
  define "Constant" [
    regex "\\\".*\\\""],

  define "Relation" [
    regex "[a-z][a-zA-Z0-9]*"],

  define "Variable" [
    regex "[A-Z][a-zA-Z0-9]*"],

-- <program> ::= <fact> <program> | <rule> <program> | ɛ
  define "Program" [
    star (alts[
      "Fact",
      "Rule"])],
--    list["Fact", "Program"],
--    list["Rule", "Program"],
--    nil],

-- <fact> ::=  <relation> "(" <constant-list> ")."
  define "Fact" [
    list["Relation", lparen, "ConstantList", rparen, period]],

-- <rule> ::= <atom> ":-" <atom-list> "."
  define "Rule" [
    list["Atom", entail, "AtomList", period]],

-- <atom> ::= <relation> "(" <term-list> ")"
  define "Atom" [
    list["Relation", lparen, "TermList", rparen]],

-- <atom-list> ::= <atom> | <atom> "," <atom-list>
  define "AtomList" [
    "single">: "Atom",
    "multiple">: list["Atom", comma, "AtomList"]],

-- <term> ::= <constant> | <variable>
  define "Term" [
    "Constant",
    "Variable"],

-- <term-list> ::= <term> | <term> "," <term-list>
  define "TermList" [
    "single">: "Term",
    "multiple">: list["Term", comma, "TermList"]],

-- <constant-list> ::= <constant> | <constant> "," <constant-list>
  define "ConstantList" [
    "single">: "Constant",
    "multiple">: list["Constant", comma, "ConstantList"]]]
