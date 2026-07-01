/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import Parser

/-!
  The string `BNF.bnf` below represents BNF syntax in BNF. In this example, we
  will write a BNF parser and verify that it can correctly parse its own
  syntax!

  There are many BNF variants and there is no official one. The common feature
  of these variants is that BNF syntax avoids parentheses and has only two
  combinators: concatenation and alternative. Rule identifiers must consist
  only of letters, numbers and hyphens `-` and must start with a letter.
  Each rule is terminated by an end-of-line marker.

  The BNF variant below simplifies the syntax for literals by only allowing
  single-quoted literals and single quotes within literals must be doubled.
  Thus `''''` represents one single quote and `''''''` represents two. The
  characters that can occur in literals are limited to ASCII letters, digits,
  and a selected list of symbols. Literals can also contain end-of-line
  marker.
-/

namespace BNF

/-- String representation of BNF syntax -/
protected def bnf : String :=
-- All the line breaks are significant!
"<syntax> ::= <rule> | <rule> <syntax>
<rule> ::= <spaces> '<' <name> '>' <spaces> '::=' <spaces> <expr-alt> <line-end>
<expr-alt> ::= <expr-cat> | <expr-cat> <spaces> '|' <expr-alt>
<expr-cat> ::= <spaces> <term> | <spaces> <term> <expr-cat>
<term> ::= '''' <text> '''' | '<' <name> '>'
<text> ::= '' | <text-character> <text>
<text-character> ::= <character> | ''''''
<name> ::= <letter> <name-string>
<name-string> ::= '' | <name-character> <name-string>
<name-character> ::= <letter> | <digit> | '-'
<line-end> ::= <spaces> <eol> | <spaces> <eol> <line-end>
<character> ::= <letter> | <digit> | <symbol>
<letter> ::= 'A' | 'B' | 'C' | 'D' | 'E' | 'F' | 'G' | 'H' | 'I' | 'J' | 'K' | 'L' | 'M' | 'N' | 'O' | 'P' | 'Q' | 'R' | 'S' | 'T' | 'U' | 'V' | 'W' | 'X' | 'Y' | 'Z' | 'a' | 'b' | 'c' | 'd' | 'e' | 'f' | 'g' | 'h' | 'i' | 'j' | 'k' | 'l' | 'm' | 'n' | 'o' | 'p' | 'q' | 'r' | 's' | 't' | 'u' | 'v' | 'w' | 'x' | 'y' | 'z'
<digit> ::= '0' | '1' | '2' | '3' | '4' | '5' | '6' | '7' | '8' | '9'
<symbol> ::= '|' | ' ' | '!' | '#' | '$' | '%' | '&' | '(' | ')' | '*' | '+' | ',' | '-' | '.' | '/' | ':' | ';' | '>' | '=' | '<' | '?' | '@' | '[' | ']' | '^' | '_' | '`' | '{' | '}' | '~' | <eol>
<spaces> ::= '' | ' ' <spaces>
<eol> ::= '
'
"

/-!
  ## BNF Syntax Tree ##
-/

/-- Type for <term> -/
inductive Term
| rule : String → Term
| literal : String → Term
deriving Repr, Inhabited

instance : ToString Term where
  toString
  | .rule name => "<" ++ name ++ ">"
  | .literal str => "'" ++ str.replace "'" "''" ++ "'"

/-- Type for <expr-cat> -/
inductive ExprCat where
| pure : Term → ExprCat
| cons : Term → ExprCat → ExprCat
deriving Repr, Inhabited

instance : ToString ExprCat :=
  let rec pp : ExprCat → String
  | .pure e => toString e
  | .cons e es => toString e ++ " " ++ pp es
  ⟨pp⟩

/-- Type for <expr-alt> -/
inductive ExprAlt where
| pure : ExprCat → ExprAlt
| cons : ExprCat → ExprAlt → ExprAlt
deriving Repr, Inhabited

instance : ToString ExprAlt :=
  let rec pp : ExprAlt → String
  | .pure l => toString l
  | .cons l ls => toString l ++ " | " ++ pp ls
  ⟨pp⟩

/-- Type for <syntax> -/
inductive Syntax where
| pure : String → ExprAlt → Syntax
| cons : String → ExprAlt → Syntax → Syntax
deriving Repr, Inhabited

instance : ToString Syntax :=
  let rec pp : Syntax → String
  | .pure n e => s!"<{n}> ::= {toString e}\n"
  | .cons n e stx => s!"<{n}> ::= {toString e}\n" ++ pp stx
  ⟨pp⟩

/-!
  ## BNF Parser ##
-/

/-- BNF parser monad -/
abbrev BNFParser (s : String.Slice) := SimpleParser s Char s.Pos

namespace BNFParser
open Parser Char

/-- Parser for <eol> -/
def eol : BNFParser s Char :=
  withErrorMessage "<eol>" do
    Parser.Char.eol

/-- Parser for <spaces>  -/
def spaces : BNFParser s Unit :=
  withErrorMessage "<spaces>" do
    dropMany (char ' ')

/-- Parser for <symbol> -/
def symbol : BNFParser s Char :=
  let list := ['|', ' ', '!', '#', '$', '%', '&', '(', ')', '*', '+', ',', '-', '.', '/', ':', ';',
    '>', '=', '<', '?', '@', '[', ']', '^', '_', '`', '{', '}', '~', '\n']
  withErrorMessage "<symbol>" do
    tokenFilter list.elem

/-- Parser for <digit> -/
def digit : BNFParser s Char :=
  withErrorMessage "<digit>" do
    ASCII.numeric

/-- Parser for <letter> -/
def letter : BNFParser s Char :=
  withErrorMessage "<letter>" do
    ASCII.alpha

/-- Parser for <character> -/
def character : BNFParser s Char :=
  withErrorMessage "<character>" do
    ASCII.alphanum <|> symbol

/-- Parser for <line-end> -/
def lineEnd : BNFParser s Unit :=
  withErrorMessage "<line-end>" do
    dropMany (spaces <* eol)

/-- Parser for <name-character> -/
def nameCharacter : BNFParser s Char :=
  withErrorMessage "<name-character>" do
    ASCII.alphanum <|> char '-'

/-- Parser for <name-string> -/
def nameString : BNFParser s String :=
  withErrorMessage "<name-string>" do
    foldl String.push "" nameCharacter

/-- Parser for <name> -/
def name : BNFParser s String :=
  withErrorMessage "<name>" do
    let a ← letter
    let s ← nameString
    return a.toString ++ s

/-- Parser for <text-character> -/
def textCharacter : BNFParser s Char :=
  withErrorMessage "<text-character>" do
    character <|> char '\'' *> char '\''

/-- Parser for <text> -/
partial def text : BNFParser s String :=
  withErrorMessage "<text>" do
    foldl String.push "" textCharacter

/-- Parser for <term> -/
def term : BNFParser s Term :=
  let literal : BNFParser s String := char '\'' *> text <* char '\''
  let rule : BNFParser s String := char '<' *> name <* char '>'
  withErrorMessage "<term>" do
    Term.literal <$> literal <|> Term.rule <$> rule

/-- Parser for <expr-cat> -/
partial def exprCat : BNFParser s ExprCat :=
  withErrorMessage "<expr-cat>" do
    let expr ← spaces *> term
    ExprCat.cons expr <$> exprCat
      <|> return ExprCat.pure expr

/-- Parser for <expr-alt> -/
partial def exprAlt : BNFParser s ExprAlt :=
  withErrorMessage "<expr-alt>" <| do
    let expr ← exprCat
    ExprAlt.cons expr <$> (spaces *> char '|' *> exprAlt)
      <|> return ExprAlt.pure expr

/-- Parser for <rule> -/
def rule : BNFParser s (String × ExprAlt) :=
  withErrorMessage "<rule>" do
    let name ← spaces *> char '<' *> name <* char '>'
    let _ ← spaces *> chars "::="
    let expr ← exprAlt <* lineEnd
    return (name, expr)

/-- Parser for <syntax> -/
partial def «syntax» : BNFParser s Syntax :=
  withErrorMessage "<syntax>" do
    let (name, expr) ← withErrorMessage "<syntax>: expected rule" rule
    Syntax.cons name expr <$> «syntax»
      <|> return Syntax.pure name expr

end BNFParser

/-- Parse BNF from string -/
def parse (input : String) : Except String BNF.Syntax :=
  match (BNFParser.syntax <* Parser.endOfInput).run (s := input.toSlice) with
  | .ok _ stx => .ok stx
  | .error _ err => .error ("error: " ++ toString err)

section Test

/-- Parsed BNF syntax -/
protected def stx : IO BNF.Syntax :=
  match BNF.parse BNF.bnf with
  | .ok stx => return stx
  | .error e => IO.println e *> return default

#eval show IO Bool from do
  let stx ← BNF.stx
  return toString stx == BNF.bnf -- round trip?

end Test

end BNF
