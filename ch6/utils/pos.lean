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

-- 4.2. Type Classes and Polymorphism
#check (IO.println)
#check @IO.println
-- def List.sum [Add α] [OfNat α 0] : List α → α
--   | [] => 0
--   | x :: xs => x + xs.sum
def fourNats := [1,2,3,4]
#eval fourNats.sum
def fourPos : List Pos := [1,2,3,4]
-- #eval fourPos.sum

-- distinct ordinary implicit arguments and instance implicit(s) (arguments)
-- instance taking instance implicit args
structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr
instance [Add α] : Add (PPoint α) where
  add p1 p2 := { x := p1.x + p2.x, y := p1.y + p2.y}
-- example of recursive structure values :
-- Add (PPoint Nat)
-- it contains a reference to the instance of Add Nat

-- declaring a type class really results in the following:
-- A structure type to contain the implementation of each overloaded operation
-- A namespace with the same name as the class
-- For each method, a function in the class's namespace that retrieves its implementation from an instance
#check @OfNat.ofNat
-- This means that each argument to the type class must be an argument to the method
-- that occurs before the instance.

-- 4.3. Controlling Instance Search
def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos
instance : HAdd Pos Nat Pos where
  hAdd := addPosNat
#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

-- class HPlus (α : Type) (β : Type) (γ : Type) where
class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α → β → γ
instance : HPlus Nat Pos Pos where
  hPlus := addNatPos
instance : HPlus Pos Nat Pos where
  hPlus := addPosNat
#eval HPlus.hPlus (3 : Pos) (5 : Nat)
#eval (HPlus.hPlus (3 : Pos) (5 : Nat): Pos)

-- Default Instances
@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add
#eval  HPlus.hPlus (3: Nat) (5: Nat)
#check  HPlus.hPlus  (5: Nat) (3: Nat)
#check HPlus.hPlus (5: Nat)
-- Similarly, simply writing 5 gives a Nat rather than a type with a metavariable that
-- is waiting for more information in order to select an OfNat instance. This is because
-- the OfNat instance for Nat is a default instance.

-- Default instances can also be assigned priorities that affect which will be chosen in
-- situations where more than one might apply. For more information on default instance
-- priorities, please consult the Lean manual.
