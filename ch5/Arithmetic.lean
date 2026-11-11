-- 5.2. Arithmetic in Monads
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op
inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)
  open Expr in
open Arith in
-- 14 / (45 - 5 * 9)
def fourteenDivided : Expr Arith :=
  prim div (const 14) (prim minus (const 45) (prim times (const 5) (const 9)))

def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m] (applyDiv : Int → Int → m Int) : Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2

#eval evaluateM applyDivExcept fourteenDivided
#eval evaluateM applyDivOption fourteenDivided

-- Further Effects
-- adding other operator as other effects
inductive Prim (special : Type) where
  | plus
  | minus
  | times
  | other : special → Prim special

inductive CanFail where
  | div
def divOption : CanFail → Int → Int → Option Int
  | CanFail.div, x, y => if y == 0 then none else pure (x / y)
def divExcept : CanFail → Int → Int → Except String Int
  | CanFail.div, x, y =>
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)
def applyPrim' [Monad m] (applySpecial : special → Int → Int → m Int) : Prim special → Int → Int → m Int
  | Prim.plus, x, y => pure (x + y)
  | Prim.minus, x, y => pure (x - y)
  | Prim.times, x, y => pure (x * y)
  | Prim.other op, x, y => applySpecial op x y
def evaluateM' [Monad m] (applySpecial : special → Int → Int → m Int): Expr (Prim special) → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM' applySpecial e1 >>= fun v1 =>
    evaluateM' applySpecial e2 >>= fun v2 =>
    applyPrim' applySpecial p v1 v2
open Expr in
open Prim in
def fourteenDivided' : Expr (Prim CanFail) :=
  (prim (other CanFail.div)) (const 14) ( prim minus (const 45) ( prim times (const 5) (const 9)))
#eval evaluateM' divExcept fourteenDivided'
#eval evaluateM' divOption fourteenDivided'

-- No Effects
-- infinite loops and throwing exceptions
def applyEmpty [Monad m] (op : Empty) (_ : Int) (_ : Int) : m Int :=
  nomatch op
open Expr Prim in
#eval evaluateM' (m := Id) applyEmpty (prim plus (const 5) (const (-14)))

-- Nondeterministic Search
-- backtrack and try a different input

-- using multiset of values, with a prim `choose` added
-- · Constants `n` evaluate to singleton sets `n`
-- · Arithmetic operators other than division are called
-- on each pair from the Cartesian product of the operators,
-- so `X+Y` evaluates to `{x+y∣x∈X,y∈Y}`
-- · Division `X/Y` evaluates to `{x/y∣x∈X,y∈Y,y≠0}`.
-- In other words, all 0 values in Y are thrown out.
-- · A choice choose(x,y) evaluates to {x,y}.

-- A monad that represents this non-deterministic effect must be able to
-- represent a situation in which there are no answers, and a situation in
-- which there is at least one answer together with any remaining answers:
inductive Many (α : Type) where
  | none : Many α
  | more : α → (Unit → Many α) → Many α
def Many.one (x : α) : Many α := Many.more x (fun () => Many.none)
def Many.union : Many α → Many α → Many α
  | Many.none, ys => ys
  | Many.more x xs, ys => Many.more x (fun () => union (xs ()) ys)

def Many.fromList : List α → Many α
  | [] => Many.none
  | x :: xs => Many.more x (fun () => fromList xs)
def Many.take : Nat → Many α → List α
  | 0, _ => []
  | _ + 1, Many.none => []
  | n + 1, Many.more x xs => x :: (xs ()).take n
def Many.takeAll : Many α → List α
  | Many.none => []
  | Many.more x xs => x :: (xs ()).takeAll

-- In a nondeterministic search, sequencing two operations consists of taking all
-- possibilities from the first step and running the rest of the program on each
-- of them, taking the union of the results.
def Many.bind : Many α → (α → Many β) → Many β
  | Many.none, _ =>
    Many.none
  | Many.more x xs, f =>
    (f x).union (bind (xs ()) f)
instance : Monad Many where
  pure := Many.one
  bind := Many.bind

-- finds all the combinations of numbers in a list that add to 15:
def addsTo (goal : Nat) : List Nat → Many (List Nat)
  | [] => if goal == 0 then pure [] else Many.none
  | x :: xs => if x > goal
    then addsTo goal xs
    else (addsTo goal xs).union (addsTo (goal - x) xs >>= fun ans =>
      pure (x::ans))

-- arithmetic evaluator that produces multisets of results
inductive NeedsSearch
  | div
  | choose
def applySearch : NeedsSearch → Int → Int → Many Int
  | NeedsSearch.choose, x, y =>
    Many.fromList [x, y]
  | NeedsSearch.div, x, y =>
    if y == 0 then
      Many.none
    else Many.one (x / y)

open Expr Prim NeedsSearch
-- 1+choose(2,5)
#eval (evaluateM' applySearch (prim plus (const 1) (prim (other choose)
  (const 2) (const 5)))).takeAll
-- 1+2/0
#eval (evaluateM' applySearch (prim plus (const 1) (prim (other div)
  (const 2) (const 0)))).takeAll
-- 90/(choose(-5,5)+5)
#eval (evaluateM' applySearch (prim (other div) (const 90) (prim plus
  (prim (other choose) (const (-5)) (const 5)) (const 5)))).takeAll

-- Custom Environments
-- evaluator can be made user-extensible by allowing strings to be used as
-- operators, and then providing a mapping from strings to a function that
-- implements them.

/-!
- Constants `n` evaluate to constant functions `fun _ => n`.
- Arithmetic operators evaluate to functions that pass their arguments
  through, so `f + g` evaluates to `fun e => f e + g e`.
- Custom operators evaluate to the result of applying the custom
  operator to the arguments, so `f OP g` evaluates to:

      fun e =>
        if e contains (OP, h) then
          h (f e) (g e)
        else
          0

  Here, `0` serves as a fallback in case an unknown operator is applied.
-/

-- 'rho' indicate the environments
def Reader (ρ : Type) (α : Type) : Type := ρ → α
def read : Reader ρ ρ := fun env => env

def Reader.pure (x : α) : Reader ρ α := fun _ => x
def Reader.bind {ρ : Type} {α : Type} {β : Type}
  (result : ρ → α) (next : α → ρ → β) : ρ → β :=
  fun env => next (result env) env
instance : Monad (Reader ρ) where
  pure x := fun _ => x
  bind x f := fun env => f (x env) env

-- custom environment type
abbrev Env : Type := List (String × (Int → Int → Int))
def exampleEnv : Env := [("max", max), ("mod", (· % ·))]
-- List.lookup on map as a list of pairs
def applyPrimReader (op : String) (x : Int) (y : Int) : Reader Env Int :=
  read >>= fun env =>
  match env.lookup op with
  | none => pure 0
  | some f => pure (f x y)
open Expr Prim in
#eval evaluateM' applyPrimReader (prim (other "max")
  (prim plus (const 5) (const 4))
  (prim times (const 3) (const 2))
) exampleEnv
