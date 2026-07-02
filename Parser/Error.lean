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
protected class Parser.Error (ε σ : Type _) [Parser.Stream σ] where
  unexpected : Stream.Position σ → Option (Stream.Token σ) → ε
  addMessage : ε → Stream.Position σ → String → ε
attribute [inherit_doc Parser.Error] Parser.Error.unexpected Parser.Error.addMessage

namespace Parser.Error

/-- *Trivial error type*

This error type simply discards all error information. This is useful for parsers that cannot fail,
or where parsing errors are intended to be handled by other means.
-/
abbrev Trivial := Unit

instance (σ) [Parser.Stream σ] : Parser.Error Trivial σ where
  unexpected _ _ := ()
  addMessage e _ _ := e

/-- *Basic error type*

This error type records the position and, optionally, the offending token where a parsing error
occurred; any additional information is discarded. This is useful for parsers where the cause of
parsing errors is predictable and only the position of the error is needed for processing.
-/
abbrev Basic σ [Parser.Stream σ] := Stream.Position σ × Option (Stream.Token σ)

instance (σ) [Parser.Stream σ] : Parser.Error (Basic σ) σ where
  unexpected p t := (p, t)
  addMessage e _ _ := e

instance (σ) [Parser.Stream σ] [Repr (Stream.Position σ)] [Repr (Stream.Token σ)] :
  ToString (Basic σ) where
  toString
    | (pos, some tok) => s!"unexpected input {repr tok} at {repr pos}"
    | (pos, none) => s!"unexpected input at {repr pos}"

/-- *Simple error type*

This error type simply records all the error information provided, without additional processing.
Users are expected to provide any necessary post-processing. This is useful for parser development.
-/
inductive Simple σ [Parser.Stream σ]
  /-- Unexpected input at position -/
  | unexpected : Stream.Position σ → Option (Stream.Token σ) → Simple σ
  /-- Add error message at position -/
  | addMessage : Simple σ → Stream.Position σ → String → Simple σ

-- The derive handler for `Repr` fails, this is a workaround.
protected def Simple.reprPrec {σ} [Parser.Stream σ] [Repr (Stream.Position σ)]
    [Repr (Stream.Token σ)] : Simple σ → Nat → Std.Format
  | unexpected pos a, prec =>
    Repr.addAppParen
      (Std.Format.group
        (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.text "Parser.Error.Simple.unexpected" ++
            Std.Format.line ++
            reprArg pos ++
            Std.Format.line ++
            reprArg a)))
      prec
  | addMessage e pos msg, prec =>
    Repr.addAppParen
      (Std.Format.group
        (Std.Format.nest (if prec >= max_prec then 1 else 2)
          (Std.Format.text "Parser.Error.Simple.addMessage" ++
            Std.Format.line ++
            Simple.reprPrec e max_prec ++
            Std.Format.line ++
            reprArg pos ++
            Std.Format.line ++
          reprArg msg)))
      prec

instance (σ) [Parser.Stream σ] [Repr (Stream.Position σ)] [Repr (Stream.Token σ)] :
    Repr (Simple σ) where
  reprPrec := Simple.reprPrec

protected def Simple.toString {σ} [Parser.Stream σ] [Repr (Stream.Position σ)]
    [Repr (Stream.Token σ)] : Simple σ → String
  | unexpected pos (some tok) => s!"unexpected token {repr tok} at {repr pos}"
  | unexpected pos none => s!"unexpected token at {repr pos}"
  | addMessage e pos msg => Simple.toString e ++ s!"; {msg} at {repr pos}"

instance (σ) [Parser.Stream σ] [Repr (Stream.Position σ)] [Repr (Stream.Token σ)] :
    ToString (Simple σ) where
  toString := Simple.toString

instance (σ) [Parser.Stream σ] : Parser.Error (Simple σ) σ where
  unexpected := Simple.unexpected
  addMessage := Simple.addMessage

end Parser.Error
