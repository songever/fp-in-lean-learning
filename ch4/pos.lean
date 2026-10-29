-- 4.1. Positive Numbers
inductive Pos : Type where
  | one: Pos
  | succ : Pos → Pos

def seven : Pos :=
  Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ (Pos.succ Pos.one)))))
-- def fourteen : Pos := seven + seven
-- def fortyNine : Pos := seven * seven

class Plus (α : Type) where
  plus : α → α → α
instance : Plus Nat where
  plus := Nat.add
open Plus (plus)
#eval plus 5 3

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k => Pos.succ k
  | Pos.succ n, k => Pos.succ (n.plus k)
instance : Plus Pos where
  plus := Pos.plus
-- def fourteen : Pos := seven + seven

-- Overloaded Addition
instance : Add Pos where
  add := Pos.plus
def fourteen : Pos := seven + seven
#eval fourteen

-- Conversion to Strings
def posToString (atTop : Bool) (p : Pos) : String :=
  let paren s := if atTop then s else "(" ++ s ++ ")"
  match p with
  | Pos.one => "Pos.one"
  | Pos.succ n => paren s!"Pos.succ {posToString false n}"
instance : ToString Pos where
  toString := posToString true
#eval s!"There are {seven}"

def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1
instance : ToString Pos where
  toString x := toString (x.toNat)
#eval s!"There are {seven}"

-- Overloaded Multiplication
def Pos.mul : Pos → Pos → Pos
  | Pos.one, k => k
  | Pos.succ n, k => n.mul k + k
instance : Mul Pos where
  mul := Pos.mul
#eval [seven * Pos.one, seven * seven, Pos.succ Pos.one * seven]

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n
def eight : Pos := 8
#eval eight
-- def zero : Pos := 0
