/-
Copyright © 2022-2025 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Parser.Prelude

public section

/-! # Parser Stream

Parsers read input tokens from a stream. To help with error reporting and backtracking, the
`Parser.Stream` class extends the basic `Stream` class with functionality to save and restore
stream positions.

The simple way to implement backtracking after a parsing error is to first save the stream state
before parsing and, upon encountering an error, restore the saved stream state. The issue with this
strategy is that each backtrack point adds a reference to the entire stream state. This prevents
linear use of the stream state. The `Parser.Stream` class allows users to work around this issue.
The `Parser.Stream.Position` type is intended to store just enough information to *reconstruct* the
stream state at a save point without having to save the entire stream state.
-/

/-- *Parser stream class*

This class extends the basic `Stream` class with position features needed by parsers for
backtracking and error reporting.

* The type `Position` is used to record position data for the stream type.
* `getPosition (s : σ) : Position` returns the current position of stream `s`.
* `setPosition (s : σ) (p : Position) : σ` restores stream `s` to position `p`.

Implementations should try to make the `Position` type as lightweight as possible for `getPosition`
and `setPosition` to work properly. Often `Position` is just a scalar type or another simple type.
This may allow for parsers to use the stream state more efficiently.
-/

protected class Parser.Stream.{u_1} (σ : Type _) (τ : outParam (Type _)) where
  Position : σ → Type u_1
  start (s : σ) : Position s
  next? (s : σ) : Position s → Option (τ × Position s)
attribute [reducible, inherit_doc Parser.Stream] Parser.Stream.Position
attribute [inherit_doc Parser.Stream] Parser.Stream.next?

instance {σ τ} [Parser.Stream σ τ] (s : σ) : Inhabited (Parser.Stream.Position s) where
  default := Parser.Stream.start s

namespace Parser.Stream

/-- Stream segment type. -/
@[expose]
def Segment {σ τ} [Parser.Stream σ τ] (s : σ) := Stream.Position s × Stream.Position s

/-- Default wrapper to make a `Parser.Stream` from a plain `Stream`.

This wrapper uses the entire stream state as position information; this is not efficient. Always
prefer tailored `Parser.Stream` instances to this default.
-/
@[expose]
def mkDefault (σ τ) [Std.Stream σ τ] := σ

@[reducible]
instance (σ τ) [self : Std.Stream σ τ] : Parser.Stream (mkDefault σ τ) τ where
  Position _ := σ
  start s := s
  next? _ := self.next?

/- redundant
@[reducible]
instance {s : String} : Parser.Stream s Char where
  Position := s.Pos
  next? p :=
   match h : p.next? with
    | some p' => (p.get (String.Pos.ne_endPos_of_next?_eq_some h), p')
    | none => none
-/

@[reducible]
instance : Parser.Stream String.Slice Char where
  Position s := s.Pos
  start s := s.startPos
  next? _ p :=
   match h : p.next? with
    | some p' => (p.get (String.Slice.Pos.ne_endPos_of_next?_eq_some h), p')
    | none => none

-- Substring.Raw is a legacy function, so maybe this should be removed.
@[reducible]
instance : Parser.Stream Substring.Raw Char where
  Position _ := String.Pos.Raw
  start s := s.startPos
  next? s p :=  if s.startPos < s.stopPos then
      some (s.startPos.get s.str, p.next s.str)
    else
      none

@[reducible]
instance (τ) : Parser.Stream (Subarray τ) τ where
  Position _ := Nat
  start s := s.start
  next? s p := s[p]? >>= (· , p  + 1)

@[reducible]
instance : Parser.Stream ByteSlice UInt8 where
  Position _ := Nat
  start s := s.start
  next? s p := s[p]? >>= (· , p  + 1)

/-
/-- `OfList` is a view of a list stream that keeps track of consumed tokens. -/
structure OfList (τ : Type _) where
  /-- Remaining tokens. -/
  next : List τ
  /-- Consumed tokens. -/
  past : List τ := []

/-- Restore a list stream to a given position. -/
def OfList.setPosition {τ} (s : OfList τ) (p : Nat) : OfList τ :=
  if s.past.length < p then
    fwd (p - s.past.length) s
  else
    rev (s.past.length - p) s
where
  /-- Internal for `OfList.setPosition`. -/
  fwd : Nat → OfList τ → OfList τ
    | k+1, ⟨x :: rest, past⟩ => fwd k ⟨rest, x :: past⟩
    | _, s => s
  /-- Internal for `OfList.setPosition`. -/
  rev : Nat → OfList τ → OfList τ
    | k+1, ⟨rest, x :: past⟩ => rev k ⟨x :: rest, past⟩
    | _, s => s

/-- Make a `Parser.Stream` from a `List`. -/
def mkOfList {τ} (data : List τ) (pos : Nat := 0) : OfList τ :=
  OfList.setPosition { next := data } pos

@[reducible]
instance (τ) : Parser.Stream (OfList τ) τ where
  Position := Nat
  getPosition s := s.past.length
  setPosition := OfList.setPosition
  next? s :=
    match s with
    | ⟨x :: rest, past⟩ => some (x, ⟨rest, x :: past⟩)
    | _ => none
-/

@[reducible]
instance (τ) : Parser.Stream (List τ) τ where
  Position _ := List τ
  start s := s
  next? _ p := p.next?

end Parser.Stream
