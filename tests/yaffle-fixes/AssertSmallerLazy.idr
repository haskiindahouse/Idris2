module Assert
%default total

data LL : Type -> Type where
  One  : a -> LL a
  Cons : a -> Lazy (LL a) -> LL a

pick : LL Nat -> Nat -> Nat
pick (One x)                 _ = x
pick wh@(Cons x (Delay rest)) k =
  if k < 5 then x else pick (assert_smaller wh rest) (k `minus` 5)
