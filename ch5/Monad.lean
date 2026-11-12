-- 5.1 The Monad Type Class
-- class Monad (m : Type → Type) where
--   pure : α → m α
--   bind : m α → (α → m β) → m β
import State
import WithLog
import BinTree

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x
instance : Monad (Except ε) where
  pure x := Except.ok x
  bind attempt next :=
    match attempt  with
    | Except.error e => Except.error e
    | Except.ok v => next v
def firstThirdFifthSeventh [Monad m] (lookup : List α → Nat → m α) (xs : List α) : m (α × α × α × α):=
  lookup xs 0 >>= fun first =>
  lookup xs 2 >>= fun third =>
  lookup xs 4 >>= fun fifth =>
  lookup xs 6 >>= fun seventh =>
  pure (first, third, fifth, seventh)

def slowMammals : List String :=
  ["Three-toed sloth", "Slow loris"]
def fastBirds : List String := [
  "Peregrine falcon",
  "Saker falcon",
  "Golden eagle",
  "Gray-headed albatross",
  "Spur-winged goose",
  "Swift",
  "Anna's hummingbird"
]
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) slowMammals
#eval firstThirdFifthSeventh (fun xs i => xs[i]?) fastBirds

def getOrExcept (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not founc (maximum is {xs.length - 1})"
  | some x => Except.ok x
#eval firstThirdFifthSeventh getOrExcept slowMammals
#eval firstThirdFifthSeventh getOrExcept fastBirds

-- General Monad Operations
def mapM [Monad m] (f : α → m β) : List α → m (List β)
  | [] => pure []
  | x :: xs =>
    f x >>= fun hd =>
    mapM f xs >>= fun tl =>
    pure (hd :: tl)
-- the return type of f determines which Monad instance will be used

instance : Monad (State σ) where
  pure x := fun s => (s, x)
  bind first next :=
    fun s =>
      let (s', x) := first s
      next x s'
def increment (howMuch : Int) : State Int Int :=
  get >>= fun i =>
  set (i + howMuch) >>= fun () =>
  pure i
#eval mapM increment [1, 2, 3, 4, 5] 0

instance : Monad (WithLog logged) where
  pure x := {log := [], val := x}
  bind result next :=
    let {log := thisOut, val := thisRes} := result
    let {log := nextOut, val := nextRes} := next thisRes
    {log := thisOut ++ nextOut, val := nextRes}
def saveIfEven (i : Int) : WithLog Int Int :=
  (if isEven i then save i else pure ()) >>= fun () =>
  pure i
#eval mapM saveIfEven [1, 2, 3, 4, 5]

-- The Identity Monad
-- def Id (t : Type) : Type := t
instance : Monad Id where
  pure x := x -- Id α === α
  bind x f := f x
#eval mapM (m := Id) (· + 1) [1,2,3,4,5]
-- Lean requires a hint that the intended monad,
-- Omitting the hint results in an error:
-- #eval mapM (· + 1) [1,2,3,4,5]
-- #eval mapM (fun x => x) [1,2,3,4,5]

-- The Monad Contract
-- 1. pure should be a left identity of bind:
--    bind (pure v) f === f v
-- 2. pure should be a right identity of bind:
--    bind v pure === v
-- 3. bind should be associative
--    bind (bind v f) g === bind v (fun x => bind (f x) g)

-- Exercises
def BinTree.mapM [Monad m] (f : α → m β) : BinTree α → m (BinTree β)
  | BinTree.leaf => pure BinTree.leaf
  | BinTree.branch l x r =>
    mapM f l >>= fun mleft =>
    f x >>= fun mthis =>
    mapM f r >>= fun mright =>
    pure (BinTree.branch mleft mthis mright)
