-- 7.2. A Monad Construction Kit

-- def OptionT (m : Type u → Type v) (α : Type u) : Type v :=
--   m (Option α)
def getSomeInput : OptionT IO String := do
  let input ← (← IO.getStdin).getLine
  let trimmed := input.trimAscii
  if trimmed == "" then
    failure
  else pure trimmed.copy

structure UserInfo where
  name : String
  favoriteBeetle : String

def getUserInfo : OptionT IO UserInfo := do
  IO.println "What is your name?"
  let name ← getSomeInput
  IO.println "What is your favorite species of beetle?"
  let beetle ← getSomeInput
  pure ⟨name, beetle⟩

def interact : IO Unit := do
  match ← getUserInfo with
  | none => IO.eprintln "Missing info"
  | some ⟨name, beetle⟩ => IO.println s!"Hello {name}, whose favorite beetle is {beetle}"

-- def OptionT.mk (x : m (Option α)) : OptionT m α := x
-- def OptionT.run (x : OptionT m α) : m (OptionT α) := x
instance [Monad m] : Monad (OptionT m) where
  pure x := OptionT.mk (pure (some x))
  bind action next := OptionT.mk do
    match ← action with
    | none => pure none
    | some v => next v

instance [Monad m] : Alternative (OptionT m) where
  failure := OptionT.mk (pure none)
  orElse x y := OptionT.mk do
    match ← x with
    | some result => pure (some result)
    | none => y ()
instance [Monad m] : MonadLift m (OptionT m) where
  monadLift action := OptionT.mk do
    pure (some (← action))

-- def StateT (σ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
--   σ → m (α × σ)
instance [Monad m] : Monad (StateT σ m) where
  pure x := fun s => pure (x, s)
  bind result next := fun s => do
    let (v, s') ← result s
    next v s'

structure LetterCounts where
  vowels : Nat
  consonants : Nat
deriving Repr
inductive Err where
  | notALetter : Char → Err
deriving Repr

def vowels :=
  let lowerVowers := "aeiouy"
  lowerVowers ++ lowerVowers.map (·.toUpper)
def consonants :=
  let lowerConsonants := "bcdfghjklmnpqrstvwxz"
  lowerConsonants ++ lowerConsonants.map (·.toUpper)

def countLetters1 (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      let st ← get
      let st' ←
        if c.isAlpha then
          if vowels.contains c then
            pure {st with vowels := st.vowels + 1}
          else if consonants.contains c then
            pure {st with consonants := st.consonants + 1}
          else  -- modified or non-English letter
            pure st
        else throw (.notALetter c)
      set st'
      loop cs
  loop str.toList
-- It would be very easy to write set st instead of set st'. In a large program,
-- this kind of mistake can lead to difficult-to-diagnose bugs.

def countLetters2 (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else  -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList
-- def modify [MonadState σ m] (f : σ → σ) : m Unit :=
--   modifyGet fun s => ((), f s)
-- class MonadState (σ : outParam (Type u)) (m : Type u → Type v) : Type (max (u+1) v) where
--   get : m σ
--   set : σ → m σ
--   modify : (σ → α × σ) → m α
-- PUnit is a version of the Unit type that is universe-polymorphic to allow it to be
-- in Type u instead of Type.


-- 7.3. Ordering Monad Transformers

def countLetters [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        else  -- modified or non-English letter
          pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList

abbrev M1 := StateT LetterCounts (ExceptT Err Id)
abbrev M2 := ExceptT Err (StateT LetterCounts Id)

-- In the case of M1, the outermost constructor is Except.ok, and
-- it contains a pair of the unit constructor with the final state.
#eval countLetters (m := M1) "hello" ⟨0, 0⟩
-- In the case of M2, the outermost constructor is the pair, which
-- contains Except.ok applied only to the unit constructor.
#eval countLetters (m := M2) "hello" ⟨0, 0⟩

-- Only one monad yields a count of vowels and consonants when the
-- string causes an exception to be thrown:
#eval countLetters (m := M1) "hello!" ⟨0, 0⟩
#eval countLetters (m := M2) "hello!" ⟨0, 0⟩

-- another program that compute different answers in M1 and M2:
def countWithFallback
  [Monad m] [MonadState LetterCounts m] [MonadExcept Err m]
  (str : String) : m Unit :=
  try
    countLetters str
  catch _ =>
    countLetters "Fallback"

-- always success on different results.
#eval countWithFallback (m := M1) "hello" ⟨0, 0⟩
#eval countWithFallback (m := M2) "hello" ⟨0, 0⟩

-- Fail with only the letter counts from "Fallback":
#eval countWithFallback (m := M1) "hello!" ⟨0, 0⟩
-- Fail with letter counts from both "hello" and "Fallback":
#eval countWithFallback (m := M2) "hello!" ⟨0, 0⟩
-- In M1, throwing and exception "rolls back" the state to where
-- the exception was caught.
-- M1 : LetterCounts → Except Err (α × LetterCounts)
-- In M2, modification to the state persist across the throwing
-- and catching of exceptions.
-- M1 : LetterCounts → Except Err α × LetterCounts

-- 7.4. More do Features

-- When an `if` is a statement in a do-block, rather than being an expression, then
-- `else pure ()` can simply be omitted, and Lean inserts it automatically.
def countLetters' [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  let rec loop (chars : List Char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
      else throw (.notALetter c)
      loop cs
  loop str.toList

-- to count the entries in a list that satisfy some monadic check:
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then
      modify (· + 1)
    -- else then pure ()
    count p xs
-- the converse of count:
def countNot [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    unless ← p x do
      modify (· + 1)
    countNot p xs

-- Early Return
def List.myfind0? (p : α → Bool) : List α → Option α
  | [] => none
  | x :: xs =>
    if p x then
      some x
    else
      myfind0? p xs
-- aborts the execution with return
def List.myfind1? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs => do
    if p x then return x
    myfind1? p xs
-- Behind the scenes, early return in Lean is implemented using a version of `ExceptT`.
-- Each do-block that uses early return is wrapped in an exception handler.
-- to make it concrete:
def runCatch [Monad m] (action : ExceptT α m α) : m α := do
  match ← action with
  | Except.ok x => pure x
  | Except.error x => pure x
-- replace early returns with `throw`
def List.myfind2? (p : α → Bool) : List α → Option α
  | [] => failure
  | x :: xs =>
    runCatch do
      if p x then throw x else pure ()
      monadLift (myfind2? p xs)

-- see another examples of early return of CLI tool on `EarlyReturn.lean`

-- Loops
-- looping over a container type in some monad:
-- class ForM (m : Type u → Type v) (γ : Type w₁) (α : outParam (Type w₂)) where
--   forM [Monad m] : γ → (α → m PUnit) → m PUnit
-- γ is the collection to be looped over
-- α is the type of elements from the collection

def List.myforM [Monad m] : List α → (α → m PUnit) → m PUnit
  | [], _ => pure ()
  | x :: xs, action => do
    action x
    forM xs action
instance [Monad m] : ForM m (List α) α where
  forM := List.myforM

def countLetters'' [Monad m] [MonadState LetterCounts m] [MonadExcept Err m] (str : String) : m Unit :=
  forM str.toList fun c => do
    if c.isAlpha then
      if vowels.contains c then
        modify fun st => {st with vowels := st.vowels + 1}
      else if consonants.contains c then
        modify fun st => {st with consonants := st.consonants + 1}
    else throw (.notALetter c)

structure AllLessThan where
  num : Nat
def AllLessThan.forM [Monad m] (coll : AllLessThan) (action : Nat → m Unit) : m Unit :=
  let rec countdown : Nat → m Unit
    | 0 => pure ()
    | n + 1 => do
      action n
      countdown n
    countdown coll.num
instance [Monad m] : ForM m AllLessThan Nat where
  forM := AllLessThan.forM
#eval forM {num := 5 : AllLessThan} IO.println

-- another ForM example that works only in a particular monad is the one
-- that loops over the lines read from an IO stream, see `ForMIO.lean`

-- Stopping Iteration
def OptionT.exec [Applicative m] (action : OptionT m α) : m Unit :=
  action *> pure ()
def countToThree (n : Nat) : IO Unit :=
  let nums : AllLessThan := ⟨n⟩
  OptionT.exec (forM nums fun i => do
    if i < 3 then failure else IO.println i)
#eval countToThree 7

instance [Monad m] : ForIn m AllLessThan Nat where
  forIn := ForM.forIn
def countToThree' (n : Nat) : IO Unit := do
  let nums : AllLessThan := ⟨n⟩
  for i in nums do
    if i < 3 then break
    IO.println i
#eval countToThree' 7
def List.myfind3? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if p x then return x
  failure
def List.myfind4? (p : α → Bool) (xs : List α) : Option α := do
  for x in xs do
    if not (p x) then continue
    return x
  failure

def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i
#eval fourToEight

def parallelLoop := do
  for x in ["currant", "gooseberry", "rowan"], y in [4:8] do
    IO.println (x, y)
#eval parallelLoop

-- Mutable Variables
-- mutable variables desugar to a use of StateT
--- use Identity monad Id to enable do-syntax without any effects
def two : Nat := Id.run do
  let mut x := 0
  x := x + 1
  x := x + 1
  return x
#eval two
--- equivaluent using StateT to add 1 twice:
def two' : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0
  result
#eval two'

def three : Nat := Id.run do
  let mut x := 0
  for _ in [1, 2, 3] do
    x := x + 1
  return x
def three' : Nat :=
  let block : StateT Nat Id Nat := do
    forM [1, 2, 3] fun _ =>
      modify (· + 1)
    return (← get)
  let (res, _) := block 0
  res
#eval three
#eval three'
def six : Nat := Id.run do
  let mut x := 0
  for y in [1, 2, 3] do
    x := x + y
  return x
def six' : Nat :=
  let block : StateT Nat Id Nat := do
    forM [1, 2, 3] fun y =>
        modify (· + y)
    return (← get)
  (block 0).fst
#eval six
#eval six'

def List.mycount (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  for x in xs do
    if p x then found := found + 1
  return found
-- `for`-loops can't be replaced by othewise-equivalent recursive helper functions
def List.mycount' (p : α → Bool) (xs : List α) : Nat := Id.run do
  let mut found := 0
  -- the found mutated is in inner monad Id, which is not transformed with StateT
  -- only the do-block in which the variable is introduced is transformed with StateT
  let rec go : List α → Id Unit
    | [] => pure ()
    | y :: ys => do
      if p y then found := found + 1
      go ys
  return found

-- What counts as a do block
example : Id Unit := do
  let mut x := 0
  x := x + 1

example : Id Unit := do
  let mut x := 0
  let other := do
    x := x + 1
  other
-- a do-block that occurs under a let-statement that defines
-- a name using ← is considered part of the surrounding block:
example : Id Unit := do
  let mut x := 0
  let other ← do
    x := x + 1
  pure other

-- do-blocks that occur as arguments to functions are independent
-- of their surrounding blocks.
example : Id Unit := do
  let mut x := 0
  let addFour (y : Id Nat) := Id.run y + 4
  addFour do
    x := 5

-- If the do keyword is completely redundant, then it does not introduce a new block.
example : Id Unit := do
  let mut x := 0
  do x := x + 1
-- he contents of branches under a do (such as those introduced by match or if) are
-- considered to be part of the surrounding block, whether or not a redundant do is
-- added.
-- Similarly, the do that occurs as part of the for and unless syntax is just part
-- of their syntax, and does not introduce a fresh do-block.
