module Tot2
%default total

data LL : Type -> Type where
  LNil  : LL a
  LCons : a -> Lazy (LL a) -> LL a

data All' : (a -> Type) -> LL a -> Type where
  ANil  : All' p LNil
  ACons : {0 x : a} -> {0 xs : Lazy (LL a)} -> p x -> Lazy (All' p xs) -> All' p (LCons x xs)

-- mirror negAnyAll: structural recursion on the IMPLICIT {xs} via lazy tail
mkAll : {xs : LL a} -> ((x : a) -> p x) -> All' p xs
mkAll {xs=LNil}            f = ANil
mkAll {xs=LCons x (Delay ys)} f = ACons (f x) (mkAll f)
