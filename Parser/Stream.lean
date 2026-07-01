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

/- *Parser stream class*

This class extends the basic `Stream` class with position features needed by parsers for
backtracking and error reporting.

* The type `Position` is used to record position data for the stream type.
* `getPosition (s : σ) : Position` returns the current position of stream `s`.
* `setPosition (s : σ) (p : Position) : σ` restores stream `s` to position `p`.

Implementations should try to make the `Position` type as lightweight as possible for `getPosition`
and `setPosition` to work properly. Often `Position` is just a scalar type or another simple type.
This may allow for parsers to use the stream state more efficiently.
-/

namespace Parser.Stream

/-- Stream segment type. -/
@[expose]
def Segment (σ) [Std.Stream σ τ] := σ × σ

/-- Start position of stream segment. -/
abbrev Segment.start [Std.Stream σ τ] (s : Segment σ) := s.1

/-- Stop position of stream segment. -/
abbrev Segment.stop [Std.Stream σ τ] (s : Segment σ) := s.2

end Parser.Stream
