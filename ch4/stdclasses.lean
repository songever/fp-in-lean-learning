import pos
import indexing

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

-- class Functor (f : Type → Type) where
-- map : {α β : Type} → (α → β) → f α → f β
-- mapConst {α β : Type} (x : α) (coll : f β) : f α :=
--   map (fun _ => x) coll
