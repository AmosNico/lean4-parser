/-
Copyright © 2022-2024 François G. Dorais, Kyrill Serdyuk, Emma Shroyer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

import Parser.Prelude
public import Parser.Error
public import Parser.Stream

public section

/-- Parser result type. -/
protected inductive Parser.Result ε Pos α : Type u
  /-- Result: success! -/
  | ok : Pos → α → Parser.Result ε Pos α
  /-- Result: error! -/
  | error : Pos → ε → Parser.Result ε Pos α
  deriving Inhabited, Repr

/--
`ParserT ε σ τ` is a monad transformer to parse tokens of type `τ` from the stream type `σ` with
error type `ε`.
-/
@[expose]
def ParserT ε {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos]
    (m : Type _ → Type _) (α : Type _) : Type _ := Pos → m (Parser.Result ε Pos α)

/-- Run the monadic parser `p` on input stream `s`. -/
@[inline]
def ParserT.run {σ} {s : σ} {τ Pos ε m α} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos]
    (p : ParserT ε s τ Pos m α) (pos : optParam Pos (Parser.Stream.start s)):
  m (Parser.Result ε Pos α) := p pos

instance {σ} {s : σ} {τ Pos ε m} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] [Monad m] :
  Monad (ParserT ε s τ Pos m) where
  pure x pos := return .ok pos x
  bind x f pos := x pos >>= fun
    | .ok pos a => f a pos
    | .error pos e => return .error pos e
  map f x pos := x pos >>= fun
    | .ok pos a => return .ok pos (f a)
    | .error pos e => return .error pos e
  seq f x pos := f pos >>= fun
    | .ok pos f => x () pos >>= fun
      | .ok pos x => return .ok pos (f x)
      | .error pos e => return .error pos e
    | .error pos e => return .error pos e
  seqLeft x y pos := x pos >>= fun
    | .ok pos x => y () pos >>= fun
      | .ok pos _ => return .ok pos x
      | .error pos e => return .error pos e
    | .error pos e => return .error pos e
  seqRight x y pos := x pos >>= fun
    | .ok pos _ => y () pos >>= fun
      | .ok pos y => return .ok pos y
      | .error pos e => return .error pos e
    | .error pos e => return .error pos e

instance {σ} {s : σ} {τ Pos ε m} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] [Monad m] :
  MonadExceptOf ε (ParserT ε s τ Pos m) where
  throw e pos := return .error pos e
  tryCatch p c pos := p pos >>= fun
    | .ok pos v => return .ok pos v
    | .error pos e => (c e).run pos

instance {σ} {s : σ} {τ Pos ε m} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] [Monad m] :
  OrElse (ParserT ε s τ Pos m α) where
  orElse p q pos :=
    p pos >>= fun
    | .ok pos' v => return .ok pos' v
    | .error _ _ => q () pos

instance {σ} {s : σ} {τ Pos ε m} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] [Monad m] :
  MonadLift m (ParserT ε s τ Pos m) where
  monadLift x pos := (.ok pos ·) <$> x

/--
`Parser ε σ τ` monad to parse tokens of type `τ` from the stream type `σ` with error type `ε`.
-/
abbrev Parser ε {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] :=
  ParserT ε s τ Pos Id

/-- Run parser `p` on input stream `s`. -/
@[inline]
protected def Parser.run {σ} {s : σ} {τ Pos ε α} [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos]
    (p : Parser ε s τ Pos α) (pos : optParam Pos (Parser.Stream.start s)) : Parser.Result ε Pos α :=
  p pos

/--
`TrivialParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with trivial
error handling.
-/
abbrev TrivialParserT {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] m :=
  ParserT Parser.Error.Trivial s τ Pos m

/--
`TrivialParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with trivial error
handling.
-/
abbrev TrivialParser {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] :=
  Parser Parser.Error.Trivial s τ Pos

/--
`BasicParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with basic
error handling.
-/
abbrev BasicParserT {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] m :=
  ParserT (Parser.Error.Basic s τ Pos) s τ Pos m

/--
`BasicParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with basic error handling.
-/
abbrev BasicParser {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] :=
  Parser (Parser.Error.Basic s τ Pos) s τ Pos

/--
`SimpleParserT σ τ` monad transformer to parse tokens of type `τ` from the stream `σ` with simple
error handling.
-/
abbrev SimpleParserT {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] m :=
  ParserT (Parser.Error.Simple s τ Pos) s τ Pos m

/--
`SimpleParser σ τ` monad to parse tokens of type `τ` from the stream `σ` with simple error handling.
-/
abbrev SimpleParser {σ} (s : σ) τ Pos [Parser.Stream s τ Pos] :=
  Parser (Parser.Error.Simple s τ Pos) s τ Pos

namespace Parser
variable {ε σ : Type u} {s : σ} {τ Pos m}
  [Parser.Stream s τ Pos] [Parser.Error ε s τ Pos] [Monad m] [MonadExceptOf ε m]

/-! # Stream Functions -/

/-- Get stream position from parser. -/
@[inline]
def getPosition : ParserT ε s τ Pos m Pos :=
  fun pos ↦ return .ok pos pos

/-- Set stream position from parser. -/
@[inline]
def setPosition (pos : Pos) : ParserT ε s τ Pos m PUnit := do
  fun _ ↦ return .ok pos PUnit.unit

/-- `withBacktracking p` parses `p` but does not consume any input on error. -/
@[inline]
def withBacktracking (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m α := do
  let savePos ← getPosition
  try p
  catch e =>
    setPosition savePos
    throw e

/--
`withCapture p` parses `p` and returns the output of `p` with the corresponding stream segment.
-/
def withCapture (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m (α × Stream.Segment s) := do
  let startPos ← getPosition
  let x ← p
  let stopPos ← getPosition
  return (x, startPos, stopPos)

/-! # Error Functions -/

/-- Throw error on unexpected token. -/
@[inline]
def throwUnexpected (input : Option τ := none) : ParserT ε s τ Pos m α := do
  throw (Error.unexpected s (← getPosition) input)

/-- Throw error with additional message. -/
@[inline]
def throwErrorWithMessage (e : ε) (msg : String) : ParserT ε s τ Pos m α := do
  throw (Error.addMessage s e (← getPosition) msg)

/-- Throw error on unexpected token with error message. -/
@[inline]
def throwUnexpectedWithMessage (input : Option τ := none) (msg : String) :
    ParserT ε s τ Pos m α := do
  throwErrorWithMessage (Error.unexpected s (← getPosition) input) msg

/-- Add message on parser error. -/
@[inline]
def withErrorMessage (msg : String) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m α := do
  try p catch e => throwErrorWithMessage e msg

/-! # Low-Level Combinators -/

/-! ### `foldl` family -/

@[specialize]
private partial def efoldlPAux [Inhabited ε]
  (f : β → α → ParserT ε s τ Pos m β) (p : ParserT ε s τ Pos m α) (y : β) (pos : Pos) :
  m (Parser.Result ε Pos (β × ε × Bool)) :=
  p pos >>= fun
    | .ok pos x => f y x pos >>= fun
      | .ok pos y => efoldlPAux f p y pos
      | .error _ e => return .ok pos (y, e, true)
    | .error _ e => return .ok pos (y, e, false)

/--
`foldlP f init p` folds the parser function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as the update
parser function `(p >>= f ⬝)` fails. Then the final folding result is returned along with the pair:

- `(e, true)` if the final `p` succeeds but then `f` fails reporting error `e`.
- `(e, false)` if the final `p` fails reporting error `e`.

In either case, the final `p` is not consumed. This parser never fails.
-/
@[inline]
def efoldlP (f : β → α → ParserT ε s τ Pos m β) (init : β) (p : ParserT ε s τ Pos m α) :
  ParserT ε s τ Pos m (β × ε × Bool) :=
  fun pos =>
    have : Inhabited ε := ⟨Error.unexpected s pos none⟩
    efoldlPAux f p init pos

/--
`foldlM f init p` folds the monadic function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails and
the error reported by `p` is returned along with the result of folding. This parser never fails.
-/
@[inline]
def efoldlM (f : β → α → m β) (init : β) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m (β × ε) :=
  efoldlP (fun y x => monadLift <| f y x) init p >>= fun (y,e,_) => return (y,e)

/--
`foldl f init p` folds the function `f` from left to right using `init` as an intitial value
and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails and the
error reported by `p` is returned along with the result of folding. This parser never fails.
-/
@[inline]
def efoldl (f : β → α → β) (init : β) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m (β × ε) :=
  efoldlM (fun y x => pure <| f y x) init p

/--
`foldlP f init p` folds the parser function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as the update
function `(p >>= f ·)` fails. This parser never fails.
-/
@[inline]
def foldlP (f : β → α → ParserT ε s τ Pos m β) (init : β) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m β :=
  Prod.fst <$> efoldlP f init p

/--
`foldlM f init p` folds the monadic function `f` from left to right using `init` as an intitial
value and the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails.
This parser never fails.
-/
@[inline]
def foldlM (f : β → α → m β) (init : β) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m β :=
  Prod.fst <$> efoldlM f init p

/--
`foldl f init p` folds the function `f` from left to right using `init` as an intitial value and
the parser `p` to generate inputs of type `α`. The folding ends as soon as `p` fails.
This parser never fails.
-/
@[inline]
def foldl (f : β → α → β) (init : β) (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m β :=
  Prod.fst <$> efoldl f init p

/-! ### `option` family -/

/--
`eoption p` tries to parse `p` (with backtracking) and returns:

- `Sum.inl x` if `p` returns `x`,
- `Sum.inr e` if `p`fails with error `e`.

This parser never fails.
-/
@[specialize]
def eoption (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m (Sum α ε) :=
  fun pos =>
    p pos >>= fun
    | .ok pos x => return .ok pos (.inl x)
    | .error _ e => return .ok pos (.inr e)

/--
`optionM p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns the
monadic value `default` if `p` fails. This parser never fails.
-/
@[inline]
def optionM (p : ParserT ε s τ Pos m α) (default : m α) : ParserT ε s τ Pos m α := do
  match ← eoption p with
  | .inl x => return x
  | .inr _ => default

/--
`optionD p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns
`default` if `p` fails. This parser never fails.
-/
@[inline]
def optionD (p : ParserT ε s τ Pos m α) (default : α) : ParserT ε s τ Pos m α :=
  optionM p (pure default)

/--
`option! p` tries to parse `p` (with backtracking) and returns `x` if `p` returns `x`, returns
`Inhabited.default` if `p` fails. This parser never fails.
-/
@[inline]
def option! [Inhabited α] (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m α :=
  optionD p default

/--
`option? p` tries to parse `p` and returns `some x` if `p` returns `x`, returns `none` if `p`
fails. This parser never fails.
-/
@[inline]
def option? (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m (Option α) :=
  option! (some <$> p)

/--
`optional p` tries to parse `p` (with backtracking) ignoring output or errors. This parser never
fails.
-/
@[inline]
def optional (p : ParserT ε s τ Pos m α) : ParserT ε s τ Pos m PUnit :=
  eoption p *> return

/-! ### `first` family -/

/--
`efirst ps` tries parsers from the list `ps` in order (with backtracking) until one succeeds:

- Once a parser `p` succeeds with value `x` then `some x` is returne along with the list of errors
  from all previous parsers.
- If none succeed then `none` is returned along with the list of errors of all parsers.

This parser never fails.
-/
def efirst (ps : List (ParserT ε s τ Pos m α)) : ParserT ε s τ Pos m (Option α × List ε) :=
  go ps []
where
  go : List (ParserT ε s τ Pos m α) → List ε → ParserT ε s τ Pos m (Option α × List ε)
  | [], es => return (none, es.reverse)
  | p :: ps, es => do
    match ← eoption p with
    | .inl x => return (some x, es.reverse)
    | .inr e => go ps (e :: es)

/--
`first ps` tries parsers from the list `ps` in order (with backtracking) until one succeeds and
returns the result of that parser.

The optional parameter `combine` can be used to control the error reported when all parsers fail.
The default is to only report the error from the last parser.
-/
def first (ps : List (ParserT ε s τ Pos m α)) (combine : ε → ε → ε := fun _ => id) :
  ParserT ε s τ Pos m α := do
  go ps (Error.unexpected s (← getPosition) none)
where
  go : List (ParserT ε s τ Pos m α) → ε → ParserT ε s τ Pos m α
    | [], e, pos => return .error pos e
    | p :: ps, e, pos =>
      p pos >>= fun
      | .ok pos v => return .ok pos v
      | .error _ f => go ps (combine e f) pos

end Parser
