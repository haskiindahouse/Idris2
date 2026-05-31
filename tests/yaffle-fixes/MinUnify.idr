module MinUnify

-- self-contained, total mirror of Test.DepTyCheck.Gen.Emptiness min/NoWeaker/reflexive

%default total

data E = NE | ME

Eq E where
  NE == NE = True
  ME == ME = True
  _  == _  = False

Ord E where
  compare ME NE = LT
  compare NE ME = GT
  compare _  _  = EQ

data NW : (from, to : E) -> Type where
  NN : NW NE NE
  AS : NW e ME

refl : {x : E} -> NW x x
refl {x=NE} = NN
refl {x=ME} = AS

minNEleft : (em : E) -> min NE em = em
minNEleft NE = Refl
minNEleft ME = Refl

minMEleft : (em : E) -> min ME em = ME
minMEleft NE = Refl
minMEleft ME = Refl

minNW : NW a1 a2 -> NW b1 b2 -> NW (min a1 b1) (min a2 b2)
minNW NN nw = rewrite minNEleft b1 in rewrite minNEleft b2 in nw
minNW AS _  = rewrite minMEleft b2 in AS

-- THE TRIGGERS (mirror minNoWeakerLeft / minNoWeakerRight)
minNWLeft : {c : _} -> NW a b -> NW (min a c) (min b c)
minNWLeft nw = minNW nw refl

minNWRight : {c : _} -> NW a b -> NW (min c a) (min c b)
minNWRight nw = minNW refl nw
