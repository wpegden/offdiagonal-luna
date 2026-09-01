import Tablet.OldPairDigraph
import Tablet.TransitiveTournament

-- [TABLET NODE: OldPairDigraphProperties]
theorem OldPairDigraphProperties
    (G : LoopGraph) (s : Nat)
    (htri : ∀ (a b : Fin s → G.vertex),
      (∀ i, ¬ G.adj (a i) (b i)) →
      (∀ ⦃i j : Fin s⦄, i.val < j.val → G.adj (a i) (b j)) → False) :
    (∀ u : (OldPairDigraph G).vertex,
        ¬ (OldPairDigraph G).arc u u) ∧
      ¬ Nonempty (TransitiveTournament (OldPairDigraph G) s) := by
-- BODY
  sorry
