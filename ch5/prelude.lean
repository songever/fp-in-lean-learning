-- 5. Monads

-- Checking for none: Don't Repeat Yourself
def first (xs : List α) : Option α :=
  xs[0]?
def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some a => next a
-- In Lean, functions don't need to be enclosed in parentheses when passed as arguments.
def firstThird' (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

-- Infix Operator
-- The number following the colon declares the precedence of the new infix operator.
infixl:55 " ~~> " => andThen
#eval 3 + 5
def firstThirdInfix (xs : List α) : Option (α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  some (first, third)
def firstThirdFifthSeventh (xs : List α) : Option (α × α × α × α) :=
  xs[0]? ~~> fun first =>
  xs[2]? ~~> fun third =>
  xs[4]? ~~> fun fifth =>
  xs[6]? ~~> fun seventh =>
  some (first, third, fifth, seventh)

-- Propagating Error Message
