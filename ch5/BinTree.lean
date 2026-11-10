inductive BinTree (α: Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α
