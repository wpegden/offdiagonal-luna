import Tablet.LooplessDigraph

-- [TABLET NODE: TransitiveTournament]
structure TransitiveTournament (D : LooplessDigraph) (s : Nat) where
-- BODY
  vertex : Fin s → D.vertex
  injective : Function.Injective vertex
  forwardArc : ∀ ⦃i j : Fin s⦄, i.val < j.val → D.arc (vertex i) (vertex j)
