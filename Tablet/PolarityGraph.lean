import Tablet.LoopGraph
import Mathlib.LinearAlgebra.Projectivization.Cardinality
import Mathlib.LinearAlgebra.Projectivization.Constructions

open scoped LinearAlgebra.Projectivization

-- [TABLET NODE: PolarityGraph]
noncomputable def PolarityGraph (K : Type) [Field K] [Fintype K]
    (t : Nat) : LoopGraph := by
-- BODY
  classical
  exact {
    vertex := Projectivization K (Fin (t + 1) → K)
    fintype := Fintype.ofFinite _
    adj := Projectivization.orthogonal
    decidableAdj := inferInstance
    symmetric := by
      intro u v
      exact Projectivization.orthogonal_comm
  }
