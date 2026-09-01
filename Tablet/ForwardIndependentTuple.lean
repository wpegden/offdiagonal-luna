import Tablet.LooplessDigraph

-- [TABLET NODE: ForwardIndependentTuple]
structure ForwardIndependentTuple (D : LooplessDigraph) (k : Nat) where
-- BODY
  vertex : Fin k → D.vertex
  independent : ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ D.arc (vertex i) (vertex j)
