import Tablet.LoopGraph

-- [TABLET NODE: IndependentWitness]
structure IndependentWitness (G : LoopGraph) (k : Nat) where
-- BODY
  vertex : Fin k → G.vertex
  injective : Function.Injective vertex
  independent : ∀ ⦃i j : Fin k⦄, i ≠ j → ¬ G.adj (vertex i) (vertex j)
