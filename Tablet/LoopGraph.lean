import Tablet.Preamble

-- [TABLET NODE: LoopGraph]
structure LoopGraph where
-- BODY
  vertex : Type
  fintype : Fintype vertex
  adj : vertex → vertex → Prop
  decidableAdj : DecidableRel adj
  symmetric : ∀ u v, adj u v ↔ adj v u
