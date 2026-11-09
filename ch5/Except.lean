-- 5. Monads

-- Propagating Error Message
-- inductive Except (ε : Type) (α : Type) where
--   | error : ε → Except ε α
--   | ok : α → Except ε α
-- deriving BEq, Hashable, Repr

def ok (x : α) : Except ε α := Except.ok x
def fail (err : ε) : Except ε α := Except.error err
def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => fail s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => ok x
def ediblePlants : List String :=
  ["ramsons", "sea plantain", "sea buckthorn", "garden nasturtium"]
#eval get ediblePlants 2
#eval get ediblePlants 4

-- def first (xs : List α) : Except String α :=
--   get xs 0
def andThen (attempt : Except e α) (next : α → Except e β) : Except e β :=
  match attempt with
  | Except.error msg => Except.error msg
  | Except.ok x => next x
def firstThird' (xs: List α) : Except String (α × α) :=
  andThen (get xs 0) fun first =>
  andThen (get xs 2) fun third =>
  Except.ok (first, third)

infixl:55 " ~~> " => andThen

def firstThird (xs : List α) : Except String (α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  ok (first, third)
def firstThirdFifthSeventh (xs : List α) : Except String (α × α × α × α) :=
  get xs 0 ~~> fun first =>
  get xs 2 ~~> fun third =>
  get xs 4 ~~> fun fifth =>
  get xs 6 ~~> fun seventh =>
  ok (first, third, fifth, seventh)
