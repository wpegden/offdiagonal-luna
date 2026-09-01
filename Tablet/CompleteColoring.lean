import Tablet.Preamble

-- [TABLET NODE: CompleteColoring]
structure CompleteColoring (n ell : Nat) where
-- BODY
  color : Fin n → Fin n → Fin ell
  symmetric : ∀ u v, color u v = color v u
