structure WithLog (logged : Type) (α : Type) where
  log : List logged
  val : α

def save (data : α) : WithLog α Unit :=
  {log := [data], val := ()}

def isEven (i : Int) : Bool :=
  i % 2 == 0
