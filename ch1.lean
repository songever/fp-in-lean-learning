-- 1.1. Evaluating Expressions
#eval String.append "Hello, "  "Lean!"
#eval String.append "great " (String.append "oak " "tree")
#eval String.append "it is " (if 1>2 then "yes" else "no")

-- 1.2. Types
#eval (1 + 2: Nat)
#check (1 - 2: Int)
#check String.append "hello" [" ", "world"]

-- 1.3. Functions and Definitions
def hello := "Hello"
def lean : String := "Lean"
#eval String.append hello (String.append " " lean)

def add1 (n: Nat) : Nat := n + 1
#eval add1 7

def maximum (n: Nat) (k: Nat) : Nat :=
  if n < k then
    k
  else n

#eval maximum (5 + 8) (2 * 7)
#check (maximum)
#check maximum

def Str : Type := String
def aStr : Str := "This is a string."

def NaturalNumber : Type := Nat
def thirtySeven : NaturalNumber := 37
def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N : Type := Nat
def thirtyNine : N := 39

-- 1.4. Structures
#check 1.2
#check -454.2123215
#check 0.0
#check 0
#check (0 : Nat)

structure Point where
  x : Float
  y : Float
deriving Repr

def origin : Point := { x := 0.0, y := 0.0 }
#eval (origin, origin.x, origin.y)

def addPoints (p1: Point) (p2: Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }
def distance (p1: Point) (p2: Point) : Float :=
  Float.sqrt ((p2.x - p1.x) ^ 2 + (p2.y - p1.y) ^ 2)
#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0}

structure Point3D where
  x : Float
  y : Float
  z : Float
deriving Repr
def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }
#check { x := 0.0, y := 0.0 }
#check { x := 0.0, y := 0.0 : Point}

def zeroX (p: Point) : Point :=
  { p with x := 0 }
def fourAndThree : Point :=
  { x := 4.3, y := 3.4 }
#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree

#check (Point.mk)
#check (Point.x)
#check (Point.y)
-- override the default mk constructor:
-- structure Point where
--   point ::
--   x : Float
--   y : Float
-- deriving Repr

-- accessor notation
#eval "one string".append " and another"
-- modifyBoth defined in the Point namespace
def Point.modifyBoth (f : Float → Float) (p: Point) : Point :=
  { x := f p.x, y := f p.y }
#eval fourAndThree.modifyBoth Float.floor

-- 1.5. Datatypes, Patterns and Recursion
def isZero (n: Nat) : Bool :=
  match n with
  | Nat.zero => true
  | _ => false
#eval isZero 0
#eval isZero 4

def pred (n: Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k
#eval pred 839
#eval pred 0

def even (n: Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)
#eval even 571
#eval even 0

def plus (n: Nat) (k: Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')
#eval plus 3 2

def times (n: Nat) (k: Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n: Nat) (k: Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

-- 1.6. Polymorphism
structure PPoint (α: Type) where
  x: α
  y: α
deriving Repr
def natOrigin : PPoint Nat :=
  { x := Nat.zero, y := Nat.zero }

def replaceX (α: Type) (point: PPoint α) (newX: α) : PPoint α :=
  { point with x := newX }
#check (replaceX)
#check replaceX Nat
#check replaceX Nat natOrigin
#check replaceX Nat natOrigin 5

def replaceX_2 {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }
#eval replaceX_2 natOrigin 5

inductive Sign where
  | pos
  | neg

def posOrNegThree (s: Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3: Nat)
  | Sign.neg => (-3: Int)
#eval posOrNegThree Sign.pos

def primesUnder10 : List Nat := [2,3,5,7]
def length {α : Type} (xs: List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length ys)
#eval length primesUnder10
#eval primesUnder10.length
#check List.length (α := Int)

#eval primesUnder10.head?
#eval [].head? (α := Int)
#eval ([] : List Int).head?

def PetName : Type := String ⊕ String
def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]
def howManyDogs (pets: List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals
