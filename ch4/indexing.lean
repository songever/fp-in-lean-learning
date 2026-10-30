-- To import pos.lean, launch a fresh VS Code session from that folder with:
-- export LEAN_PATH="$PWD"
-- code .
import pos
#check Pos

-- 4.4. Arrays and Indexing
def northernTrees: Array String :=
  #["sloe", "birch", "elm", "oak"]

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [
    "Long-legged Sac Spider",
    "Wolf Spider",
    "Hobo Spider",
    "Cat-faced Spider"
  ]
}

def NonEmptyList.get? : NonEmptyList α → Nat → Option α
  | xs, 0 => some xs.head
  | xs, n + 1 => xs.tail.get?Internal n

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length
theorem atLeastThreeSpiders : idahoSpiders.inBounds 2 := by simp [idahoSpiders]
theorem notSixSpiders : ¬idahoSpiders.inBounds 5 := by simp [idahoSpiders]
def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok: xs.inBounds i) :=
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

-- Overloading Indexing
-- class GetElem (coll: Type) (idx: Type) (item: outParam Type) (inBounds: outParam (coll → idx → Prop)) where
--   getElem : (c : coll) → (i : idx) → inBounds c i → item
instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get
#eval idahoSpiders[0]
-- #eval idahoSpiders[9]

instance : GetElem (List α) Pos α (fun list n => list.length > n.toNat) where
  getElem (xs: List α) (i: Pos) ok := xs[i.toNat]
#eval [1,2,3,4][(2: Pos)]

instance : GetElem (PPoint α) Bool α (fun _ _ => True) where
  getElem (p: PPoint α) (i: Bool) _ :=
    if not i then p.x else p.y
#eval (⟨3,4⟩ : PPoint Nat)[true]
