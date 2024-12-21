module Hydra.Sources.Tier4.Ext.Go.Syntax where

import Hydra.Kernel
import Hydra.Dsl.Grammars
import Hydra.Tools.GrammarToModule
import qualified Data.List as L
import qualified Hydra.Dsl.Annotations as Ann
import qualified Hydra.Grammar as G

goModule :: Module
goModule = grammarToModule ns goGrammar $
    Just ("A Go syntax module. Based on the Go Programming Language Specification Extended BNF variant, as of December 15, 2022:\n" ++
      "  https://go.dev/ref/spec.")
  where
    ns = Namespace "hydra/ext/go/syntax"

goGrammar :: G.Grammar
goGrammar = G.Grammar $ productions

amp_             = terminal "&"
amp_equal_       = terminal "&="
amp_hat_         = terminal "&^"
amp_hat_equal_   = terminal "&^="
assign_          = terminal ":="
close_curly_     = terminal "}"
close_paren_     = terminal ")"
close_square_    = terminal "]"
colon_           = terminal ":"
comma_           = terminal ","
dot_             = terminal "."
double_amp_      = terminal "&&"
double_equal_    = terminal "=="
double_gt_       = terminal ">>"
double_gt_equal_ = terminal ">>="
double_lt_       = terminal "<<"
double_lt_equal_ = terminal "<<="
double_minus_    = terminal "--"
double_pipe_     = terminal "||"
double_plus_     = terminal "++"
ellipsis_        = terminal "..."
endmarker_       = terminal "" 
equal_           = terminal "="
gt_              = terminal ">"
gte_             = terminal ">="
hat_equal_       = terminal "^="
left_arrow_      = terminal "<-"
lt_              = terminal "<"
lte_             = terminal "<="
minus_           = terminal "-"
minus_equal_     = terminal "-="
not_             = terminal "!"
not_equal_       = terminal "!="
open_curly_      = terminal "{"
open_paren_      = terminal "("
open_square_     = terminal "["
percent_         = terminal "%"
percent_equal_   = terminal "%="
pipe_            = terminal "|"
pipe_equal_      = terminal "|="
plus_            = terminal "+"
plus_equal_      = terminal "+="
semi_            = terminal ";"
slash_           = terminal "/"
slash_equal_     = terminal "/="
star_            = terminal "*"
star_equal_      = terminal "*="
tilde_           = terminal "~"
underscore_      = terminal "_" 

--TODO: figure out if we need to separately define specific tokens
--tokens :: [G.Production]

-- The spec uses Wirth syntax notation, describing it as follows:
-- Syntax      = { Production } .
-- Production  = production_name "=" [ Expression ] "." .
-- Expression  = Term { "|" Term } .
-- Term        = Factor { Factor } .
-- Factor      = production_name | token [ "…" token ] | Group | Option | Repetition .
-- Group       = "(" Expression ")" .
-- Option      = "[" Expression "]" .
-- Repetition  = "{" Expression "}" .
-- |   alternation
-- ()  grouping
-- []  option (0 or 1 times)
-- {}  repetition (0 to n times)

productions :: [G.Production]
productions = [
--TODO: figure out how to represent the following:
--newline        = /* the Unicode code point U+000A */ .
--unicode_char   = /* an arbitrary Unicode code point except newline */ .
--unicode_letter = /* a Unicode code point categorized as "Letter" */ .
--unicode_digit  = /* a Unicode code point categorized as "Number, decimal digit" */ .

-- Letters and digits

-- letter = unicode_letter | "_" .
  define "Letter" [
    "UnicodeLetter",
    underscore_],
    
-- decimal_digit = "0" … "9" .
    define "DecimalDigit" [
      terminal "0", terminal "1", terminal "2", terminal "3", terminal "4", terminal "5", terminal "6", terminal "7", terminal "8", terminal "9"]

-- binary_digit = "0" | "1" .
    define "BinaryDigit" [
      terminal "0", terminal "1"]

-- octal_digit = "0" … "7" .
    define "OctalDigit" [
     terminal "0", terminal "1", terminal "2", terminal "3", terminal "4", terminal "5", terminal "6", terminal "7"]

-- hex_digit = "0" … "9" | "A" … "F" | "a" … "f"
    define "HexDigit" [
      terminal "0", terminal "1", terminal "2", terminal "3", terminal "4", terminal "5", terminal "6", terminal "7", terminal "8", terminal "9"]
      terminal "A", terminal "B", terminal "C", terminal "D", terminal "E", terminal "F",
      terminal "a", terminal "b", terminal "c", terminal "d", terminal "e", terminal "f"]

-- Identifiers

-- identifier = letter { letter | unicode_digit } .
    define "Identifier" [
      list["Letter", star(alts["Letter", "UnicodeDigit"])]]

--TODO handle keywords.
--break        default      func         interface    select
--case         defer        go           map          struct
--chan         else         goto         package      switch
--const        fallthrough  if           range        type
--continue     for          import       return       var

-- Integer literals

-- int_lit = decimal_lit | binary_lit | ocal_lit | hex_lit
    define "IntLit" [
      alts["DecimalLit", "BinaryLit", "OctalLit", "HexLit"]]

-- decimal_lit = "0" | ( "1" … "9" ) [ [ "_" ] decimal_digits ] .
    define "DecimalLit" [
      alts[
        terminal "0",
        list[
          alts[terminal "1", terminal "2", terminal "3", terminal "4", terminal "5", terminal "6", terminal "7", terminal "8", terminal "9"],
          alts01[list[alts["", underscore_], "DecimalDigits"]]]]]

-- binary_lit = "0" ( "b" | "B" ) [ "_" ] binary_digits .
    define "BinaryLit" [
      list[
        terminal "0",
        alts[terminal "b", terminal "B"],
        alts01[underscore_],
        "BinaryDigits"]]

-- octal_lit = "0" [ "o" | "O" ] [ "_" ] octal_digits .
    define "OctalLit" [
      list[
        terminal "0",
        alts[terminal "o", terminal "O"],
        alts01[underscore_],
        "OctalDigits"]]

-- hex_lit = "0" ( "x" | "X" ) [ "_" ] hex_digits .
    define "HexLit" [
      list[
        terminal "0",
        alts[terminal "x", terminal "X"],
        alts01[underscore_],
        "OctalDigits"]]

-- decimal_digits = decimal_digit { [ "_" ] decimal_digit } .
    define "DecimalDigits" [
      list[
        "DecimalDigit",
        star(alts01[underscore_], "DecimalDigit")]]

-- binary_digits = binary_digit { [ "_" ] binary_digit } .
    define "BinaryDigits" [
      list[
        "BinaryDigit",
        star(alts01[underscore_], "BinaryDigit")]]

-- octal_digits = octal_digit { [ "_" ] octal_digit } .
    define "OctalDigits" [
      list[
        "OctalDigit",
        star(alts01[underscore_], "OctalDigit")]]

-- hex_digits = hex_digit { [ "_" ] hex_digit } .
    define "HexDigits" [
      list[
        "HexDigit",
        star(alts01[underscore_], "HexDigit")]]

-- Floating-point literals

-- float_lit = decimal_float_lit | hex_float_lit .
    define "FloatLit" [
      alts["DecimalFloatLit", "HexFloatLit"]]
 
-- decimal_float_lit = decimal_digits "." [ decimal_digits ] [ decimal_exponent ] |
--                     decimal_digits decimal_exponent |
--                     "." decimal_digits [ decimal_exponent ] .
    define "DecimalFloatLit" [
      alts(
        list[
          "DecimalDigits",
          dot_,
          alts01["DecimalDigits"],
          alts01["DecimalExponent"]],
        list[
          "DecimalDigits",
          "DecimalExponent"],
        list[
          dot_,
          "DecimalDigits",
          alts01["DecimalExponent"]])]

-- decimal_exponent = ( "e" | "E" ) [ "+" | "-" ] decimal_digits .
    define "DecimalExponent" [
      list[
        alts[terminal "e", terminal "E"],
        alts01[alts[plus_, minus_]],
        "DecimalDigits"]]
 
-- hex_float_lit = "0" ( "x" | "X" ) hex_mantissa hex_exponent .
    define "HexFloatLit" [
      list[
        terminal "0",
        alts[terminal "x", terminal "X"],
        "HexMantissa",
        "HexExponent"]]

-- hex_mantissa = [ "_" ] hex_digits "." [ hex_digits ] |
--                [ "_" ] hex_digits |
--                "." hex_digits .
    define "HexMantissa" [
      alts(
        list[
          alts01[underscore_],
          "HexDigits",
          dot_,
          alts01["HexDigits"]],
        list[
          alts01[underscore_],
          "HexDigits"],
        list[
          dot_,
          "HexDigits"])]

-- hex_exponent = ( "p" | "P" ) [ "+" | "-" ] decimal_digits .
    define "HexExponent" [
      list[
        alts[terminal "p", terminal "P"],
        alts01[plus_, minus_],
        "DecimalDigits"]]
