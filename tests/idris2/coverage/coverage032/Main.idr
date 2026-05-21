test : List (List a) -> List (List b) -> Nat
test x [] = 1
test [] y = 2
test ([] :: xs) (y :: ys) = 3
test (x :: xs) ([] :: ys) = 4
test ((z :: zs) :: xs) ((w :: ws) :: ys) = 5
