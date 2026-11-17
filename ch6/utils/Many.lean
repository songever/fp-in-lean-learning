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
