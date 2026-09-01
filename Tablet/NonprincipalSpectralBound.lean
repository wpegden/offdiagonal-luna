import Tablet.LoopGraph

-- [TABLET NODE: NonprincipalSpectralBound]
def NonprincipalSpectralBound (G : LoopGraph) (lambda : ℝ) : Prop :=
-- BODY
  letI : Fintype G.vertex := G.fintype
  letI : DecidableRel G.adj := G.decidableAdj
  ∀ (mu : ℝ) (v : G.vertex → ℝ),
    v ≠ 0 →
    (∑ i, v i = 0) →
    (∀ i, ∑ j, (if G.adj i j then v j else 0) = mu * v i) →
    |mu| ≤ lambda
