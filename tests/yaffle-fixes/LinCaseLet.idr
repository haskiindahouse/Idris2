module LinCaseLet

-- mirror Data.Linear.Token (ref1) locally so the repro is self-contained
0 T1 : (s : Type) -> Type
T1 s = %World

data R1 : (s, a : Type) -> Type where
  (#) : (v : a) -> (1 tok : T1 s) -> R1 s a

0 F1 : (s : Type) -> (a : Type) -> Type
F1 s a = (1 t : T1 s) -> R1 s a

-- mimic RRBVector1 lookup inner case: 2 direct `# t` branches + 1 let-threaded branch.
-- g is where-bound (like lookupTree) so the s parameter is shared.
f : Nat -> Nat -> F1 s (Maybe Nat)
f i size t =
  case compare i size of
    EQ => Nothing # t
    GT => Nothing # t
    LT =>
      let r # t := g i t
        in Just r # t
  where
    g : Nat -> F1 s Nat
    g j u = j # u
