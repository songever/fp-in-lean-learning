import BinTree
def isEven (i : Int) : Bool :=
  i % 2 == 0

def sumAndFindEvens' : List Int → List Int × Int
  | [] => ([], 0)
  | i :: is =>
    let (moreEven, sum) := sumAndFindEvens' is
    (if isEven i then i :: moreEven else moreEven, sum + i)


def inorderSum' :  BinTree Int → List Int × Int
  | BinTree.leaf => ([], 0)
  | BinTree.branch l x r =>
    let (leftVisited, leftSum) := inorderSum' l
    let (hereVisited, hereSum) := ([x], x)
    let (rightVisited, rightSum) := inorderSum' r
    (leftVisited ++ hereVisited ++ rightVisited, leftSum + hereSum + rightSum)

structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α
def andThen (result : WithLog α β) (next: β → WithLog α γ) : WithLog α γ :=
  let {log := thisOut, val := thisRes} := result
  let {log := nextOut, val := nextRes} := next thisRes
  {log := thisOut ++ nextOut, val := nextRes}
def ok (x : β) : WithLog α β := {log := [], val := x}
def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

infixl:55 " ~~> " => andThen
def sumAndFindEven : List Int → WithLog Int Int
  | [] => ok 0
  | i :: is =>
    (if isEven i then save i else ok ()) ~~> fun () =>
    sumAndFindEven is ~~> fun sum =>
    ok (i + sum)
def inorderSum : BinTree Int → WithLog Int Int
  | BinTree.leaf => ok 0
  | BinTree.branch l x r =>
    inorderSum l ~~> fun leftSum =>
    save x ~~> fun () =>
    inorderSum r ~~> fun rightSum =>
    ok (leftSum + x + rightSum)
