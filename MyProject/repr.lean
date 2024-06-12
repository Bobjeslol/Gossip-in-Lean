-- repr.lean
-- Description:
-- - Allows us to verify the correctness of the gossip representation by viewing the state.

import Mathlib.Data.Fin.Basic

def ReprState (n : Nat) : Type := Fin n → Fin n → Bool

def initialReprState (n : Nat) : ReprState n := fun i j => i = j

def Call (n : Nat) := Fin n × Fin n

def makeCall (s : ReprState n) : Call n → ReprState n
  | (i, j), x, y =>
    if x = i
    then s x y ∨ s j y
    else
      if x = j
        then s x y ∨ s i y
        else s x y

def makeCalls (s : ReprState n) (cs : List (Fin n × Fin n)) : ReprState n :=
  cs.foldl makeCall s

instance : Repr (ReprState n) := Repr.mk $
  fun s _ =>
    let whatIknows i := (i, ((Fin.list n).filter (s i)))
    repr ((Fin.list n).map whatIknows)

def calls : List (Fin 4 × Fin 4) := [(1, 2), (2, 3), (3, 0), (0, 1)]
#eval repr (initialReprState 4)
#eval repr (makeCall (initialReprState 4) (1, 3))
#eval repr (makeCalls (initialReprState 4) calls)
