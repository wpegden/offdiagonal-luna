import Tablet.CompleteColoring

-- [TABLET NODE: MonochromaticClique]
structure MonochromaticClique {n ell : Nat} (c : CompleteColoring n ell) (s : Nat) where
-- BODY
  vertex : Fin s → Fin n
  injective : Function.Injective vertex
  monochromatic : ∃ col : Fin ell, ∀ ⦃i j : Fin s⦄, i ≠ j →
    c.color (vertex i) (vertex j) = col
