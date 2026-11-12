-- 5.3. do-Notation for Monads
import BinTree
import State

-- translate Monads usage to do-notation
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α)
  (xs : List α) : m (α × α × α × α) := do
  let first ← lookup xs 0
  let third ← lookup xs 2
  let fifth ← lookup xs 4
  let seventh ← lookup xs 6
  pure (first, third, fifth, seventh)

def number (t : BinTree α) : BinTree (Nat × α) :=
    let rec helper : BinTree α → State Nat (BinTree (Nat × α))
      | BinTree.leaf => pure BinTree.leaf
      | BinTree.branch l x r => do
        let nleft ← helper l
        let k ← get
        set (k + 1)
        let nright ← helper r
        pure (BinTree.branch nleft (k, x) nright)
    (helper t 0).snd

-- with nested action
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs => do
    pure ((← f x)::(← mapM f xs))

def increment : State Nat Nat := do
  let n ← get
  set (n + 1)
  pure n
def number' (t : BinTree α) : BinTree (Nat × α) :=
  let rec helper : BinTree α → State Nat (BinTree (Nat × α))
    | BinTree.leaf => pure BinTree.leaf
    | BinTree.branch l x r => do
      pure (BinTree.branch (← helper l) ((← increment), x) (← helper r))
  (helper t 0).snd
