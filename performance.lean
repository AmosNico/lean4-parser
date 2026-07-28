import Parser.Basic
import Std.Time

def parseRange1 (start stop : Nat) :
    Parser (Parser.Error.Simple (List Nat) Nat) (List Nat) Nat Unit :=
  if start ≥ stop then return
  else
    Parser.token start *> parseRange1 (start + 1) stop

def parseRange2 (start stop : Nat) :
    Parser (Parser.Error.Simple (List Nat) Nat) (List Nat) Nat Unit :=
  if start ≥ stop then return
  else
    try
      Parser.withBacktracking (Parser.take 10 Parser.anyToken *> Parser.throwUnexpected)
    catch _ =>
      Parser.token start *> parseRange2 (start + 1) stop

abbrev List' := Parser.Stream.mkDefault (List Nat) Nat

def parseRange3 (start stop : Nat) :
    Parser (Parser.Error.Simple List' Nat) List' Nat Unit :=
  if start ≥ stop then return
  else
    Parser.token start *> parseRange3 (start + 1) stop

def parseRange4 (start stop : Nat) :
    Parser (Parser.Error.Simple List' Nat) List' Nat Unit :=
  if start ≥ stop then return
  else
    try
      Parser.withBacktracking (Parser.take 10 Parser.anyToken *> Parser.throwUnexpected)
    catch _ =>
      Parser.token start *> parseRange4 (start + 1) stop

def test1 (n : Nat) : UInt8 :=
  match Parser.run (parseRange1 0 n) (List.range n) with
  | .ok _ _ _ => 0
  | .error _ _ _ => 1

def test2 (n : Nat) : UInt8 :=
  match Parser.run (parseRange2 0 n) (List.range n) with
  | .ok _ _ _ => 0
  | .error _ _ _ => 1

def test3 (n : Nat) : UInt8 :=
  match Parser.run (parseRange3 0 n) (List.range n) with
  | .ok _ _ _ => 0
  | .error _ _ _ => 1

def test4 (n : Nat) : UInt8 :=
  match Parser.run (parseRange4 0 n) (List.range n) with
  | .ok _ _ _ => 0
  | .error _ _ _ => 1

def bench (descr : String) (p : Nat → UInt8) : IO Unit := do
  let start ← IO.monoMsNow
  let mut checksum := 0
  for _ in [0:10000] do
    checksum := checksum ||| p 1000
  let stop ← IO.monoMsNow
  IO.println s!"{descr} - result {checksum} - time {stop - start}ms"


def main : IO Unit := do
  bench "Warm-up without backtracking" test1
  bench "Warm-up with backtracking" test2
  bench "Test without backtracking" test1
  bench "Test with backtracking" test2
  bench "Test default without backtracking" test3
  bench "Test default with backtracking" test4
