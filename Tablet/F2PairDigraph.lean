import Tablet.OldPairDigraph
import Mathlib.Data.ZMod.Basic

open scoped BigOperators

-- [TABLET NODE: F2PairDigraph]
def F2PairDigraph (s : Nat) : LooplessDigraph :=
-- BODY
  let G : LoopGraph := {
    vertex := Fin (s - 1) → ZMod 2
    fintype := inferInstance
    adj := fun x y => ∑ i, x i * y i = 0
    decidableAdj := inferInstance
    symmetric := by
      intro x y
      simp [mul_comm]
  }
  OldPairDigraph G
