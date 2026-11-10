import BinTree
-- 5. Monods
-- Numbering Tree Nodes

open BinTree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)

def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper (n : Nat) : BinTree α → (Nat × BinTree (Nat × α))
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch l x r =>
      let (k, numLeft) := helper n l
      let (i, numRight) := helper (k + 1) r
      (i, BinTree.branch numLeft (k, x) numRight)
  (helper 0 t).snd

-- inputState -> (outputState, value)
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)
-- input unchanged
def ok (x : α) : State σ α :=
  fun s => (s, x)

def get : State σ σ :=
  fun s => (s, s)
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())

def andThen (first : State σ α) (next : α → State σ β) : State σ β :=
  fun s =>
    let (s', x) := first s -- input s to get α
    next x s' -- then transfer type and input s' to get β
infixl:55 " ~~> " => andThen

def number (t : BinTree α) : BinTree (Nat × α) :=
  let State := State Nat (BinTree (Nat × α))
  let rec helper : BinTree α → State
    | BinTree.leaf => (n, BinTree.leaf)
    | BinTree.branch l x r =>
      helper l ~~> fun numl =>
      get ~~> fun n =>
      set (n + 1) ~~> fun () =>
      helper r ~~> fun numr =>
      ok (BinTree.branch numl (n, x) numr)
  (helper t 0).snd
