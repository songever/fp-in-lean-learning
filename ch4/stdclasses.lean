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
