-- 5.4 The IO Monad
#print Nat
#print Char.isAlpha
#print List.isEmpty

#print IO
#print IO.Error

#print EIO
-- state wrapped in the type Void, which is an internal primitive that
-- causes a value to be erased from compiled code;
#print EST
#print EST.Out
#print EST.pure
#print EST.bind

-- Putting all of this together, `IO` is a monad that tracks state and
-- errors at the same time.
-- The collection of available errors is that given by the datatype
-- `IO.Error`, which has constructors that describe many things that
-- can go wrong in a program.
-- The state is a type that represents the real world, call `IO.RealWorld`
-- Each basic `IO` action receives this real world and returns another one,
-- paired either with an error or a result.
-- In `IO`, `pure` returns the world unchanged, while `bind` passes the modified
-- world from action into the next action

-- Because the entire universe doesn't fit in a computer's memory, the world
-- being passed around is just a representation. So long as world tokens are
-- nnot re-used, the representation is safe. this type `IO.ReadWorld` does not
-- need to contain any data at all, because it is only used inside of `Void`:
#print IO.RealWorld
