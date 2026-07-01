/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Parser.Prelude
public import Parser.Stream

public section

/-! # Parser Error

The class `Parser.Error` is used throughout the library for the purpose of reporting parser errors.
Users are encouraged to provide their own instances tailored to their applications.

Three general purpose instances are provided:

* `Parser.Error.Simple` records all parsing error information, without processing.
* `Parser.Error.Basic` just records the location of the primary parsing error.
* `Parser.Error.Trivial` discards all parsing error information.

These are intended for use in parser development and as building blocks (or inspiration) for
tailored instances.
-/

/-- *Parser error class*

This class declares an error type for a given parser stream.

Given `Parser.Stream σ τ`, `Parser.Error ε σ τ` provides two basic mechanisms for reporting parsing
errors:

* `unexpected (p : Stream.Position σ) (t : Option τ) : ε`
  is used to report an unexpected input at a given position, optionally with the offending token.
* `addMessage (e : ε) (p : Stream.Position σ) (info : String)`
  is used to add additional error information at a given position.

This class can be extended to provide additional error reporting and processing functonality, but
only these two mechanisms are used within the library.
-/
protected class Parser.Error ε {σ} (s : σ) (τ Pos : outParam (Type _)) [Parser.Stream s τ Pos] where
  unexpected : Pos → Option τ → ε
  addMessage : ε → Pos → String → ε
attribute [inherit_doc Parser.Error] Parser.Error.unexpected Parser.Error.addMessage

namespace Parser.Error

/-- *Trivial error type*

This error type simply discards all error information. This is useful for parsers that cannot fail,
or where parsing errors are intended to be handled by other means.
-/
abbrev Trivial := Unit

instance {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] : Parser.Error Trivial s τ Pos where
  unexpected _ _ := ()
  addMessage e _ _ := e

/-- *Basic error type*

This error type records the position and, optionally, the offending token where a parsing error
occurred; any additional information is discarded. This is useful for parsers where the cause of
parsing errors is predictable and only the position of the error is needed for processing.
-/
abbrev Basic {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] := Pos × Option τ

instance {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] : Parser.Error (Basic s τ Pos) s τ Pos where
  unexpected p t := (p, t)
  addMessage e _ _ := e

instance {σ} (s : σ) τ Pos [Repr τ] [Parser.Stream s τ Pos] [Repr Pos] :
  ToString (Basic s τ Pos) where
  toString
    | (pos, some tok) => s!"unexpected input {repr tok} at {repr pos}"
    | (pos, none) => s!"unexpected input at {repr pos}"

/-- *Simple error type*

This error type simply records all the error information provided, without additional processing.
Users are expected to provide any necessary post-processing. This is useful for parser development.
-/
inductive Simple {σ} (s : σ) τ Pos [Parser.Stream s τ Pos]
  /-- Unexpected input at position -/
  | unexpected : Pos → Option τ → Simple s τ Pos
  /-- Add error message at position -/
  | addMessage : Simple s τ Pos → Pos → String → Simple s τ Pos
deriving Repr

instance {s : String.Slice} : ToString s.Pos where
  toString pos := s!"position {(s.sliceTo pos).positions.length}"

protected def Simple.toString {σ} {s : σ} {τ Pos} [Repr τ] [Parser.Stream s τ Pos] [ToString Pos] :
    Simple s τ Pos → String
  | unexpected pos (some tok) => s!"unexpected token {repr tok} at {pos}"
  | unexpected pos none => s!"unexpected token at {pos}"
  | addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {pos}"

instance {σ} (s : σ) τ Pos [Repr τ] [Parser.Stream s τ Pos] [ToString Pos] :
    ToString (Simple s τ Pos) where
  toString := Simple.toString

instance {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] :
    Parser.Error (Simple s τ Pos) s τ Pos where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error
