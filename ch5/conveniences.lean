-- 5.5. Addtional Conveniences
import BinTree

-- Shared Argument Type
def equal?' [BEq α] (x: α) (y: α) : Option α :=
  if x == y then some x else none
def equal? [BEq α] (x y: α) : Option α :=
  if x == y then some x else none

-- Leading Dot Notation
def BinTree.mirror' : BinTree α → BinTree α
  | BinTree.leaf => BinTree.leaf
  | BinTree.branch l x r => BinTree.branch (mirror' r) x (mirror' l)

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

def BinTree.empty : BinTree α := .leaf
#check (.empty : BinTree Nat)

-- Or-Patterns
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

def Weekday.isWeekend1 (day : Weekday) : Bool :=
  match day with
  | Weekday.saturday => true
  | Weekday.sunday => true
  | _ => false
def Weekday.isWeekend2 (day : Weekday) : Bool :=
  match day with
  | .saturday => true
  | .sunday => true
  | _ => false
def Weekday.isWeekend3 (day : Weekday) : Bool :=
  match day with
  | .saturday | .sunday => true
  | _ => false
def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false

def condense : α ⊕ α → α
  | .inl x | .inr x => x
def stringy : Nat ⊕ Weekday → String
  | .inl x | .inr x => s!"It is {repr x}"
def getTheNat : (Nat × α) ⊕ (Nat × β) → Nat
  | .inl (n, x) | .inr (n, y) => n
-- def getTheAlpha : (Nat × α) ⊕ (Nat × α) → α
--  | .inl (n, x) | .inr (n, y) => x

-- shared pattern match by backup global variable
def str := "Some string"
def getTheString : (Nat × String) ⊕ (Nat × β) → String
  | .inl (n, str) | .inr (n, y) => str
#eval getTheString (.inl (20, "twenty") : (Nat × String) ⊕ (Nat × String))
#eval getTheString (.inr (20, "twenty"))
