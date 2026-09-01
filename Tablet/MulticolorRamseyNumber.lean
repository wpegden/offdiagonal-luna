import Tablet.Preamble
import Tablet.CompleteColoring
import Tablet.MonochromaticClique

-- [TABLET NODE: MulticolorRamseyNumber]
noncomputable def MulticolorRamseyNumber (s ell : Nat) : Nat :=
-- BODY
  sInf { n : Nat | ∀ (c : CompleteColoring n ell),
    Nonempty (MonochromaticClique c s) }
