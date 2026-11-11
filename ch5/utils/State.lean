-- inputState -> (outputState, value)
def State (σ : Type) (α : Type) : Type :=
  σ → (σ × α)

def get : State σ σ :=
  fun s => (s, s)
def set (s : σ) : State σ Unit :=
  fun _ => (s, ())
