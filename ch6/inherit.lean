structure MythicalCreature where
  large: Bool
deriving Repr
#check MythicalCreature.mk
#check MythicalCreature.large

structure Monster extends MythicalCreature where
  vulnerability : String
deriving Repr

def troll : Monster where
  large := true
  vulnerability := "sunlight"
#check Monster.mk
#eval troll.toMythicalCreature
-- def troll : Monster := <<true>, "sunlight">  -- does not works

def MythicalCreature.small (c : MythicalCreature) : Bool := !c.large
-- Dot notation take inheritance into account fro user-defined functions
#eval troll.small
-- #eval MythicalCreature.small troll

-- Multiple Inheritance
structure Helper extends MythicalCreature where
  assistance : String
  payment : String
deriving Repr
def nisse : Helper where
  assistance := "household tasks"
  payment := "porridge"
  large := false

structure MonstrousAssistant extends Monster, Helper where
deriving Repr
def domsticatedTroll : MonstrousAssistant where
  large := true
  assistance := "heavy labor"
  payment := "toy goats"
  vulnerability := "sunlight"
-- the first specified path to the grandparent structure is taken, and the additional
-- parent structures' fields are copied rather than having the new structure include
-- both parents directly.
#check MonstrousAssistant.mk
#print MonstrousAssistant.toMonster
#print MonstrousAssistant.toHelper
#print MonstrousAssistant

-- Default Declarations
inductive Size where
  | small
  | medium
  | large
deriving BEq
structure SizedCreature extends MythicalCreature where
  size : Size
  large := size == Size.large

-- To not deviate from the parent structure:
-- Defining a proposition that the fields are related appropriately, and designing
-- the API to require evidence that the proposition is true where it matters
abbrev SizesMatch (sc : SizedCreature) : Prop :=
  sc.large = (sc.size == Size.large)
def huldre : SizedCreature where
  size := .medium
example : SizesMatch huldre := by
  decide
