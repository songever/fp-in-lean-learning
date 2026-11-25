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
