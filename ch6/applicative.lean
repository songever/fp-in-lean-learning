import indexing
import Classes
import Many

-- 6.2. Applicative Functors
instance : Applicative Option where
  pure x := .some x
  seq f x :=
    match f with
    | none => none
    | some g => g <$> x ()

instance : Applicative (Except ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .error e => .error e
    | .ok g => g <$> x ()

structure Pair (α β : Type) : Type where
  first : α
  second : β
instance : Functor (Pair α) where
  map f x := ⟨x.first, f x.second⟩
-- def Pair.pure (x : β) : Pair α β := Pair.mk _ x

-- A Non-Monadic Applicative
structure RawInput where
  name : String
  birthYear : String
-- business logic;
-- 1. The name may not be empty
-- 2. The birth year must be numeric and non-negative
-- 3. The birth year must be greater than 1900, and less than or equal to the year
--    in which the form is validated

-- Subtypes
-- structure Subtype {α : Type} (p : α → Prop) where
--   val : α
--   property : p val

def FastPos : Type := {x : Nat // x > 0}
def one : FastPos := ⟨1, by decide⟩
instance : OfNat FastPos (n + 1) where
  ofNat := ⟨n + 1, by simp +arith⟩

-- Name the decidable proposition in if condition
def Nat.asFastPos? (n : Nat) : Option FastPos :=
  if h : n > 0 then
    some ⟨n, h⟩
  else none

-- Validated Input
structure CheckedInput (thisYear : Nat) : Type where
  name : {n : String // n ≠ ""}
  birthYear : {y : Nat // y > 1900 ∧ y ≤ thisYear}
deriving Repr
inductive Validate (ε α : Type) : Type where
  | ok : α → Validate ε α
  | errors : NonEmptyList ε → Validate ε α
deriving Repr

instance : Functor (Validate ε) where
  map f
    | .ok x => .ok (f x)
    | .errors errs => .errors errs
instance : Applicative (Validate ε) where
  pure x := .ok x
  seq f x :=
    match f with
    | .ok g => g <$> x ()
    | .errors errs =>
      match x () with
      | .ok _ => .errors errs
      | .errors errs' => .errors (errs ++ errs')

def Field := String
def reportError (f : Field) (msg : String) : Validate (Field × String) α :=
  .errors { head := (f, msg), tail := [] }
def checkName (name : String) : Validate (Field × String) {n : String // n ≠ ""} :=
  if h : name = "" then
    reportError "name" "Required"
  else pure ⟨name, h⟩

def Validate.andThen (val : Validate ε α) (next : α → Validate ε β) : Validate ε β :=
  match val with
  | .errors errs => .errors errs
  | .ok x => next x
def checkYearIsNat (year : String) : Validate (Field × String) Nat :=
  match year.trimAscii.toNat? with
  | none => reportError "birth year" "Must by digits"
  | some n => pure n
def checkBirthYear (thisYear year : Nat): Validate (Field × String)
  {y : Nat // y > 1900 ∧ y ≤ thisYear} :=
  if h : year > 1900 then
    if h' : year ≤ thisYear then
      pure ⟨year, by simp [*]⟩
    else reportError "birth year" s!"Must be no later then {thisYear}"
  else reportError "birth year" "Must be after 1900"
def checkInput (year : Nat) (input : RawInput) : Validate (Field × String) (CheckedInput year) :=
  pure CheckedInput.mk <*>
    checkName input.name <*>
    (checkYearIsNat input.birthYear).andThen fun birthYearAsNat =>
      checkBirthYear year birthYearAsNat

#eval checkInput 2023 {name := "David", birthYear := "1984"}
#eval checkInput 2023 {name := "", birthYear := "2045"}
#eval checkInput 2023 {name := "David", birthYear := "syzygy"}

-- 6.3. The Applicative Contract
-- For learning the Contract kept on Applicative and the relationship with Functors
-- and Monads, see the following site:
-- https://leanprover.github.io/functional_programming_in_lean/functor-applicative-monad/applicative-contract.html

-- To show why `Validate.andThen` should not be used to implement `bind` in a `Monad`:
def notFun : Validate String (Nat → String) :=
  .errors {head := "First error", tail := []}
def notArg : Validate String Nat :=
  .errors {head := "Second error", tail := []}
#eval notFun <*> notArg

def seq_bind (f : Validate ε (α → β)) (x : Unit → Validate ε α) : Validate ε β :=
  f.andThen fun g =>
  (x ()).andThen fun y =>
  pure (g y)
#eval seq_bind notFun (fun () => notArg)
-- the seq_bind implemented by the Validate.andThen as monad.bind, doesn't behave
-- the same as Validate.seq itself

-- 6.4. Alternatives
-- Recovery from Failure
abbrev NonEmptyString := {s : String // s ≠ ""}
inductive LegacyCheckedInput where
  | humanBefore1970 :
    (birthYear : {y : Nat // y > 999 ∧ y < 1970}) →
    String → LegacyCheckedInput
  | humanAfter1970 :
    (birthYear : {y : Nat // y > 1970}) →
    NonEmptyString → LegacyCheckedInput
  | company :
    NonEmptyString →
    LegacyCheckedInput
deriving Repr

-- class SeqRight (f : Type → Type) where
--   seqRight : f α → (Unit → f β) → f β
-- abbreviation: seqRight === (*>)
def checkThat (condition : Bool) (field : Field) (msg : String)
  : Validate (Field × String) Unit :=
  if condition then pure () else reportError field msg
def checkcompany (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkThat (input.birthYear == "FIRM") "birth year" "FIRM if a company" *>
  .company <$> checkName input.name

def checkSubtype {α : Type} (v : α) (p : α → Prop) [Decidable (p v)] (err : ε)
  : Validate ε {x : α // p x} :=
  if h : p v then .ok ⟨v, h⟩ else .errors {head := err, tail := []}

def checkHumanBefore1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanBefore1970 <$>
      checkSubtype y (fun x => x > 999 ∧ x < 1970) ("birth year", "less than 1970") <*>
      pure input.name

def checkHumanAfter1970 (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  (checkYearIsNat input.birthYear).andThen fun y =>
    .humanAfter1970 <$>
      checkSubtype y (· > 1970) ("birth year", "greater than 1970") <*>
      checkName input.name

-- class OrElse (α : Type) where
--   orElse : α → (Unit → α) → α
def Validate.orElse (a : Validate ε α) (b : Unit → Validate ε α) : Validate ε α :=
  match a with
  | .ok x => .ok x
  | .errors e =>
    match b () with
    | .ok x => .ok x
    | .errors e' => .errors (e ++ e')
instance : OrElse (Validate ε α) where
  orElse := Validate.orElse
def checkLegacyInput (input : RawInput) : Validate (Field × String) LegacyCheckedInput :=
  checkcompany input <|> checkHumanBefore1970 input <|> checkHumanAfter1970 input
#eval checkLegacyInput ⟨"Johnny's Troll Groomers", "FIRM"⟩
#eval checkLegacyInput ⟨"Johnny", "1963"⟩
#eval checkLegacyInput ⟨"", "1963"⟩
#eval checkLegacyInput ⟨"", "1970"⟩

-- The Alternative Class
-- class Alternative (f : Type → Type) extends Applicative f where
--   failure : f α
--   orElse : f α → (Unit → f α) → f α

-- implementors of Alternative get OrElse instances for free:
instance [Alternative f] : OrElse (f α) where
  orElse := Alternative.orElse
instance : Alternative Option where
  failure := none
  orElse
    | some x, _ => some x
    | none, x => x ()

-- Many can represent the results of a searching process
-- Many.bind pipe all results to the next function and union all the outputs
-- Many.orElse should also represent the enumeration on all results
-- the implementation follows the general structure of the Many.union:
def Many.orElse : Many α → (Unit → Many α) → Many α
  | .none, ys => ys ()
  | .more x xs, ys => .more x (fun () => orElse (xs ()) ys)
instance : Alternative Many where
  failure := .none
  orElse := Many.orElse

-- see More Applicative operations:
-- def guard [Alternative f] (p : Prop) [Decidable p] : f Unit :=
--   if p then
--     pure ()
--   else failure
-- It is very useful in monadic programs to terminate the execution early.
def Many.countdown : Nat → Many Nat
  | 0 => .none
  | n + 1 => .more n (fun () => countdown n)
def evenDivisors (n : Nat) : Many Nat := do
  -- this line give the count decreasingly
  let k ← Many.countdown (n + 1)
  -- guard result:
  -- the pure () on bind continue the process,
  -- while the failure(:= .none) break the pipe
  guard (k % 2 = 0)
  guard (n % k = 0)
  -- all the final results on every count, no matter the pure k returned below
  -- or the .none returned above, will be unioned at last by the Many.bind.
  pure k
#eval (evenDivisors 20).takeAll
