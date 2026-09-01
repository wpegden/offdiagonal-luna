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
  constructor
  · intro u
    exact u.2
  · intro ht
    rcases ht with ⟨t⟩
    let a : Fin s → G.vertex := fun i => (t.vertex i).1.1
    let b : Fin s → G.vertex := fun i => (t.vertex i).1.2
    apply htri a b
    · intro i
      exact (t.vertex i).2
    · intro i j hij
      exact t.forwardArc hij
