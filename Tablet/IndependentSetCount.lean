import Tablet.Preamble
import Tablet.LoopGraph

-- [TABLET NODE: IndependentSetCount]
noncomputable def IndependentSetCount (G : LoopGraph) (k : Nat) : Nat :=
-- BODY
  letI := G.fintype
  letI := Classical.decEq G.vertex
  letI := G.decidableAdj
  let p : Finset G.vertex → Prop := fun S =>
    S.card = k ∧ ∀ ⦃u v : G.vertex⦄, u ∈ S → v ∈ S → u ≠ v → ¬ G.adj u v
  letI : Fintype { S : Finset G.vertex // p S } :=
    Fintype.subtype (Finset.univ.filter p) (by intro S; simp [p])
  Fintype.card { S : Finset G.vertex // p S }
