import Parser.Char

open Parser

namespace Issue35

def test : Bool :=
  match Parser.run (Char.string "abc" : SimpleParser String.Slice Char String) "abc" with
  | .ok s pos r => pos == s.rawEndPos && r == "abc"
  | .error _ _ _ => false

#guard test

end Issue35
