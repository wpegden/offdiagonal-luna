import Tablet.LoopGraph

-- [TABLET NODE: CliqueWitness]
structure CliqueWitness (G : LoopGraph) (s : Nat) where
-- BODY
  vertex : Fin s → G.vertex
  injective : Function.Injective vertex
  adjacent : ∀ ⦃i j : Fin s⦄, i ≠ j → G.adj (vertex i) (vertex j)
