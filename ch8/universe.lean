-- 8.2. The Universe Design Pattern

-- codes for custom universe
inductive NatOrBool where
    | nat | bool
abbrev NatOrBool.asType (code : NatOrBool) : Type :=
    match code with
    | .nat => Nat
    | .bool => Bool

-- refine the type from the code
def decode (t : NatOrBool) (input : String) : Option t.asType :=
    -- Dependent pattern matching
    match t with
    | .nat => input.toNat?
    | .bool =>
        match input with
        | "true" => some true
        | "false" => some false
        | _ => none

-- codes for any possible nesting of the pair and natural number types:
inductive NestedPairs where
    | nat : NestedPairs
    | pair : NestedPairs → NestedPairs → NestedPairs
abbrev NestedPairs.asType : NestedPairs → Type
    | .nat => Nat
    | .pair t1 t2 => asType t1 × asType t2
-- recursion over codes is required in order to implement BEq for the universe:
def NestedPairs.beq (t : NestedPairs) (x y : t.asType) : Bool :=
    match t with
    | .nat => x == y
    | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd

instance {t : NestedPairs} : BEq t.asType where
    beq x y := t.beq x y

-- Type Classes vs Universes
-- Type classes are a convenient way to allow library code to be
-- used with more types than the original author expected.

-- A universe à la Tarski, on the other hand, restricts the API to be
-- usable only with a predeatermind collection of types. useful cases:

-- 1. When a function should act very differently depending on which type
--    it is passed--it is impossible to pattern match on types themselves,
--    but pattern matching on codes for types is allowed
-- 2. When an external system inherently limits the types of data that may
--    be provided, and extra flexibility is not desired
-- 3. When additional properties of a type are required over and above the
---   implementation of some operations

-- A Universe of Finite Types
-- Two functions whose argument type is finite can be checked for equailty by
-- enumerating all possible arguments, calling the functions on each of them,
-- and then comparing the results. Checking higher-order functions for equality
-- requires generating all possible functions of a given type, which additionally
-- requires that the return type is finite so that each element of the argument
-- type can be mapped to each element of the return type.

-- to represent finite types by a universe:
inductive Finite where
    | unit : Finite
    | bool : Finite
    | pair : Finite → Finite → Finite
    | arr : Finite → Finite → Finite
abbrev Finite.asType : Finite → Type
    | .unit => Unit
    | .bool => Bool
    | .pair t1 t2 => asType t1 × asType t2
    | .arr t1 t2 => asType t1 → asType t2
-- In this universe, the constructor `arr` stands for the function type.

-- helpers:
def List.product (xs : List α) (ys : List β) : List (α × β) := Id.run do
    let mut out : List (α × β) := []
    for x in xs do
        for y in ys do
            out := (x, y) :: out
    pure out.reverse
-- generate all functions from a finite type to some list of values
mutual
    def Finite.enumerate (t : Finite) : List t.asType :=
        match t with
        | .unit => [()]
        | .bool => [true, false]
        | .pair t1 t2 => t1.enumerate.product t2.enumerate
        | .arr t1 t2 => t1.functions t2.enumerate
    def Finite.functions (t : Finite) (results : List α) : List (t.asType → α) :=
        match t with
        | .unit => results.map fun r => fun () => r
        | .bool => (results.product results).map fun (r1, r2) =>
            fun
            | true => r1
            | false => r2
        | .pair t1 t2 =>
            let fls := t1.functions <| t2.functions results
            fls.map fun f =>
                fun (x, y) => f x y
        | .arr t1 t2 =>
            let args := t1.enumerate
            let base := results.map fun r => fun _ => r
            args.foldr (fun arg rest => (t2.functions rest).map fun more =>
                fun f => more (f arg) f)
                base
end
def Finite.beq (t : Finite) (x y : t.asType) : Bool :=
    match t with
    | .unit => true
    | .bool => x == y
    | .pair t1 t2 => beq t1 x.fst y.fst && beq t2 x.snd y.snd
    | .arr t1 t2 =>
        t1.enumerate.all fun arg => beq t2 (x arg) (y arg)
#eval Finite.beq (.arr .bool .bool) (fun _ => true) (fun b => b == b)
