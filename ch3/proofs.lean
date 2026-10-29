def OnePlusOneIsTwo : Prop := 1 + 1 = 2
theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl

-- with tactics
theorem onePlusOneIsTwo' : 1 + 1 = 2 := by
  simp

-- Connectives
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" :=
  And.intro
  rfl
  rfl
theorem addAndAppend' : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by
  simp
  rfl

theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a
theorem onePlusOneAndLessThan : 1 + 1 = 2 ∨ 3 < 5 := by simp
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by simp
theorem trueIsTrue : True := True.intro
theorem trueOrFalse : True ∨ False := by simp
theorem falseImpliesTrue : False → True := by simp

-- Evidence as Arguments
def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]
-- def oops := woodlandCritters[3]

-- def third (xs: List α) : α := xs[2]
def third (xs: List α) (ok: xs.length > 2) : α := xs[2]
#eval third woodlandCritters (by simp [woodlandCritters])

-- Indexing Without Evidence
def thirdOption (xs: List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters
#eval thirdOption ["only", "two"]
#eval woodlandCritters[1]!

-- some kinds of Error Messages:
-- only programs whose types contain at least one value are allowed to crash
def unsafeThird (xs : List α) : α := xs[2]!

-- treated as a function application
#eval woodlandCritters [1]
