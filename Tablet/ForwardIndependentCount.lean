import Tablet.Preamble
import Tablet.LooplessDigraph

-- [TABLET NODE: ForwardIndependentCount]
def ForwardIndependentCount (D : LooplessDigraph) (k : Nat) : Nat :=
-- BODY
  letI := D.fintype
  letI := D.decidableArc
  let p : (Fin k → D.vertex) → Prop := fun f => ∀ ⦃i j : Fin k⦄,
    i.val < j.val → ¬ D.arc (f i) (f j)
  letI : Fintype { f : Fin k → D.vertex // p f } :=
    Fintype.subtype (Finset.univ.filter p) (by intro f; simp [p])
  Fintype.card { f : Fin k → D.vertex // p f }
