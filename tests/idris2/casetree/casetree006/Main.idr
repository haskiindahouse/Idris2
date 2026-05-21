import Data.Vect

data IsVar : a -> Nat -> List a -> Type where
     First : IsVar n Z (n :: ns)
     Later : IsVar n i ns -> IsVar n (S i) (m :: ns)

dropIdx : {vars : _} ->
          {idx : _} ->
          (outer : List Nat) ->
          (unused : Vect (length vars) Bool) ->
          (0 p : IsVar x idx (outer ++ vars)) ->
          Int
dropIdx [] (False::_) First = 1
dropIdx [] (True::_) First = 2
dropIdx [] (False::rest) (Later p) = 3
dropIdx [] (True::rest) (Later p) = 4
dropIdx (_::xs) unused First = 5
dropIdx (_::xs) unused (Later p) = 6
