import pos
import indexing

-- 4.5 Stanard Classes

-- Equality and Ordering
def Pos.comp : Pos → Pos → Ordering
  | Pos.one, Pos.one => Ordering.eq
  | Pos.one, Pos.succ _ => Ordering.lt
  | Pos.succ _, Pos.one => Ordering.gt
  | Pos.succ n, Pos.succ m => comp n m
instance : Ord Pos where
  compare := Pos.comp

-- Hashing
class hashable (α : Type) where
  hash : α → UInt64
-- A reasonable hash function for an inductive datatype can be
-- written by assigning a unique number to each constructor, and
-- then mixing that number with the hashes of each field.
def hashPos : Pos → UInt64
  | Pos.one => 0
  | Pos.succ n => mixHash 1 (hashPos n)
instance : Hashable Pos where
  hash := hashPos

instance [Hashable α] : Hashable (NonEmptyList α) where
  hash xs := mixHash (hash xs.head) (hash xs.tail)

inductive BinTree (α: Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
def eqBinTree [BEq α] : BinTree α → BinTree α → Bool
  | BinTree.leaf, BinTree.leaf => true
  | BinTree.branch l1 x1 r1, BinTree.branch l2 x2 r2 =>
    x1 == x2 && eqBinTree l1 l2 && eqBinTree r1 r2
  | _, _ => false
instance [BEq α] : BEq (BinTree α) where
  beq := eqBinTree

def hashBinTree [Hashable α] : BinTree α → UInt64
  | BinTree.leaf => 0
  | BinTree.branch l x r => mixHash 1 (mixHash (hashBinTree l) (mixHash (hash x) (hashBinTree r)))
instance [Hashable α] : Hashable (BinTree α) where
  hash := hashBinTree

-- Deriving Standard Class
deriving instance BEq, Hashable for Pos
deriving instance BEq, Hashable, Repr for NonEmptyList

-- Appending
-- class HAppend (α : Type) (β : Type) (γ : outParam Type) where
--   hAppend : α → β → γ
instance : Append (NonEmptyList α) where
  append xs ys :=
    { head := xs.head, tail := xs.tail ++ ys.head :: ys.tail}
#eval idahoSpiders ++ idahoSpiders

instance : HAppend (NonEmptyList α) (List α) (NonEmptyList α) where
  hAppend xs ys :=
    { head := xs.head, tail := xs.tail ++ ys}
#eval idahoSpiders ++ ["Trapdoor Spider"]

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α) where
  hAppend xs ys := match xs with
    | [] => ys
    | x :: xs => { head := x, tail := xs ++ ys.head :: ys.tail}
#eval ["Trapdoor Spider"] ++ idahoSpiders

-- Functors
-- class Functor (f : Type → Type) where
-- map : {α β : Type} → (α → β) → f α → f β
-- mapConst {α β : Type} (x : α) (coll : f β) : f α :=
--   map (fun _ => x) coll

#eval Functor.map (· + 5) [1,2,3]
#eval Functor.map toString (some (List.cons 5 List.nil))
#eval Functor.map List.reverse [[1,2,3],[4,5,6]]
#eval (· + 5) <$> [1,2,3]
#eval toString <$> (some (List.cons 5 List.nil))
#eval List.reverse <$> [[1,2,3],[4,5,6]]

instance : Functor NonEmptyList where
  map f xs := {head := f xs.head, tail := f <$> xs.tail}
instance : Functor PPoint where
  map f p := { x := f p.x, y := f p.y }

-- 4.6 Coercions
-- class Coe (α : Type) (β : Type) where
-- coe : α → β

instance : Coe Pos Nat where
  coe x := x.toNat
#eval [1,2,3,4].drop (2: Pos)
#check [1,2,3,4].drop (2: Pos)

-- Chainning Coercions
def oneInt : Int := Pos.one
inductive A where
  | a
inductive B where
  | b
instance : Coe A B where
  coe _ := B.b
instance : Coe B A where
  coe _ := A.a
instance : Coe Unit A where
  coe _ := A.a
-- Lean compiler does not get stuck in the presence of circular coercions
def coercedToB : B := ()
#eval coercedToB

-- Lean stdlib defines a coercion from any type α to Option α
def List.last? : List α → Option α
  | [] => none
  | [x] => x
  | _ :: x :: xs => last? (x::xs)
def perhapsPerhapsPerhaps : Option (Option (Option String)) := "Please don't tell me"

-- Coercions are only activeated automatically when Lean encouters a mismatch between
-- an inferred type and a type that is imposed from the rest of the program.
-- def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 392
def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := (392: Nat)
-- manually coercion
def perhapsPerhapsPerhapsNat2 : Option (Option (Option Nat)) := ↑(392: Nat)

-- Non-Empty Lists and Dependent Coercions
instance : Coe (NonEmptyList α) (List α) where
  coe
    | {head := x, tail := xs} => x::xs

-- class CoeDep (α : Type) (x : α) (β : Type) where
--  coe : β
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := {head := x, tail := xs}

-- Coercing to Types
structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier
def natMulMonoid : Monoid := {Carrier := Nat, neutral := 1, op:= (· * ·)}
def natAddMonoid : Monoid := {Carrier := Nat, neutral := 0, op:= (· + ·)}
def stringMonoid : Monoid := ⟨String, "", String.append⟩
def listMonoid (α : Type) : Monoid := ⟨List α, [], List.append⟩

def foldMap_verbose (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- CoeSort coerce a type into a type that that is a Sort.
-- the term Sort in Lean refers to these types that classify other types:
-- Type classifies types that themselves classify data.
-- Prop classifies propositions that themselves classify evidence of their truth.
instance : CoeSort Monoid Type where
  coe m := m.Carrier
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- used on if expr that expects the condition to be a decidable prop
-- rather than a Bool
instance : CoeSort Bool Prop where
  coe b := b = true

-- Coercing to Functions
-- class CoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
--   coe : (x : α) → makeFunctionType x
