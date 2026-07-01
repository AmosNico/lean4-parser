/-
Copyright © 2022 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Parser.Basic
public import Parser.RegEx.Basic

public section

namespace Parser.Char
variable {σ} {s : σ} {Pos ε m} [Parser.Stream s Char Pos] [Parser.Error ε s Char Pos] [Monad m]

/-- `char tk` accepts and returns character `tk`, otherwise fails -/
@[inline]
def char (tk : Char) : ParserT ε s Char Pos m Char :=
  withErrorMessage s!"expected {repr tk}" <| token tk

/-- `chars tks` accepts and returns string `tks`, otherwise fails -/
def chars (tks : String) : ParserT ε s Char Pos m String :=
  withErrorMessage s!"expected {repr tks}" do
    let mut acc : String := ""
    for tk in tks.toList do
      acc := acc.push (← token tk)
    return acc

/-- `string tks` accepts and returns string `tks`, otherwise fails -/
def Legacy.string {s : Substring.Raw} [Parser.Error ε s Char String.Pos.Raw] (tks : String) :
    ParserT ε s Char String.Pos.Raw m String :=
  withErrorMessage s!"expected {repr tks}" do
    let start ← getPosition
    if start.offsetBy tks.rawEndPos ≤ s.stopPos ∧ String.Pos.Raw.substrEq tks 0 s.str start tks.rawEndPos.byteIdx then
      setPosition (start.offsetBy tks.rawEndPos)
      return tks
    else
      throwUnexpected

/-- `captureStr p` parses `p` and returns the output of `p` with the corresponding Substring.Raw -/
def Legacy.captureStr {s : Substring.Raw} [Parser.Error ε s Char String.Pos.Raw]
    (p : ParserT ε s Char String.Pos.Raw m α) :
    ParserT ε s Char String.Pos.Raw m (α × Substring.Raw) := do
  let (x, start, stop) ← withCapture p
  return (x, ⟨s.str, start, stop⟩)

/-- `matchStr re` accepts and returns substring matches for regex `re` groups, otherwise fails -/
def Legacy.matchStr {s : Substring.Raw} [Parser.Error ε s Char String.Pos.Raw] (re : RegEx Char) :
    ParserT ε s Char String.Pos.Raw m (Array (Option Substring.Raw)) := do
  let ms ← re.match
  return ms.map fun
    | some (start, stop) => some ⟨s.str, start, stop⟩
    | none => none

/-- `string tks` accepts and returns string `tks`, otherwise fails -/
def string (s : String.Slice) [Parser.Error ε s Char s.Pos] (tks : String) :
    ParserT ε s Char s.Pos m String :=
  withErrorMessage s!"expected {repr tks}" do
    match (s.sliceFrom (← getPosition)).skipPrefix? tks with
    | some pos =>
      setPosition (String.Slice.Pos.ofSliceFrom pos)
      return tks
    | none => throwUnexpected

/-- `captureStr p` parses `p` and returns the output of `p` with the corresponding Substring.Raw -/
def captureStr {s : String.Slice} [Parser.Error ε s Char s.Pos]
    (p : ParserT ε s Char s.Pos m α) : ParserT ε s Char s.Pos m (α × String.Slice) := do
  let (x, start, stop) ← withCapture p
  return (x, s.slice! start stop)

/-- `matchStr re` accepts and returns substring matches for regex `re` groups, otherwise fails -/
def matchStr {s : String.Slice} [Parser.Error ε s Char s.Pos] (re : RegEx Char) :
    ParserT ε s Char s.Pos m (Array (Option String.Slice)) := do
  let ms ← re.match
  return ms.map fun
    | some (start, stop) => some (s.slice! start stop)
    | none => none

/-- Parse space (U+0020) -/
@[inline]
def space : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected space (U+0020)" <| token ' '

/-- Parse horizontal tab (U+0009) -/
@[inline]
def tab : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected horizontal tab (U+0009)" <| token '\t'

/-- Parse line feed (U+000A) -/
@[inline]
def ASCII.lf : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected line feed (U+000A)" <| token '\n'

/-- Parse carriage return (U+000D) -/
@[inline]
def ASCII.cr : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected carriage return (U+000D)" <| token '\r'

/-- Parse end of line -/
@[inline]
def eol : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected newline" do
    (ASCII.cr *> ASCII.lf) <|> ASCII.lf

namespace ASCII

/-- Parse whitespace character -/
def whitespace : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected whitespace character" do
    tokenFilter fun c => c == ' ' || c >= '\t' && c <= '\r'

/-- Parse uppercase letter character (`A`..`Z`) -/
def uppercase : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected uppercase letter character" do
    tokenFilter fun c => c >= 'A' && c <= 'Z'

/-- Parse lowercase letter character (`a`..`z`)-/
def lowercase : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected lowercase letter character" do
    tokenFilter fun c => c >= 'a' && c <= 'z'

/-- Parse alphabetic character (`A`..`Z` and `a`..`z`) -/
def alpha : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected alphabetic character" do
    tokenFilter fun c => if c >= 'a' then c <= 'z' else c >= 'A' && c <= 'Z'

/-- Parse numeric character (`0`..`9`)-/
def numeric : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected decimal digit character" do
    tokenFilter fun c => c >= '0' && c <= '9'

/-- Parse alphabetic letter or digit (`A`..`Z`, `a`..`z` and `0`..`9`) -/
def alphanum : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected letter or digit character" do
    tokenFilter fun c =>
      if c >= 'a' then c <= 'z'
      else if c >= 'A' then c <= 'Z'
      else c >= '0' && c <= '9'

/-- Parse control character -/
def control : ParserT ε s Char Pos m Char :=
  withErrorMessage "expected control character" do
    tokenFilter fun c => c.val < 0x20 || c.val == 0x7f

/-- Parse decimal digit (`0`-`9`) -/
def digit : ParserT ε s Char Pos m (Fin 10) :=
  withErrorMessage "expected decimal digit" do
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then
          some ⟨val, h⟩
        else
          none

/-- Parse binary digit (`0`..`1`) -/
def binDigit : ParserT ε s Char Pos m (Fin 2) :=
  withErrorMessage "expected binary digit" do
    tokenMap fun
    | '0' => some ⟨0, Nat.zero_lt_succ 1⟩
    | '1' => some ⟨1, Nat.succ_lt_succ (Nat.zero_lt_succ 0)⟩
    | _ => none

/-- Parse octal digit (`0`..`7`) -/
def octDigit : ParserT ε s Char Pos m (Fin 8) :=
  withErrorMessage "expected octal digit" do
    tokenMap fun c =>
      if c >= '0' then
        let val := c.toNat - '0'.toNat
        if h : val < 8 then
          some ⟨val, h⟩
        else
          none
      else
        none

/-- Parse hexadecimal digit (`0`..`9`, `A`..`F` and `a`..`f`) -/
def hexDigit : ParserT ε s Char Pos m (Fin 16) :=
  withErrorMessage "expected hexadecimal digit" do
    tokenMap fun c =>
      if c < '0' then none else
        let val := c.toNat - '0'.toNat
        if h : val < 10 then
          some ⟨val, Nat.lt_trans h (by decide)⟩
        else if c < 'A' then none else
          let val := val - ('A'.toNat - '9'.toNat - 1)
          if h : val < 16 then
            some ⟨val, h⟩
          else if c < 'a' then none else
            let val := val - ('a'.toNat - 'A'.toNat)
            if h : val < 16 then
              some ⟨val, h⟩
            else
              none

end ASCII
