import Tablet.Preamble

-- [TABLET NODE: LooplessDigraph]
structure LooplessDigraph where
-- BODY
  vertex : Type
  fintype : Fintype vertex
  arc : vertex → vertex → Prop
  decidableArc : DecidableRel arc
  loopless : ∀ u, ¬ arc u u
