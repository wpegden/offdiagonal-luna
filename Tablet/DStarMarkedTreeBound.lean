import Tablet.ForwardIndependentCount
import Tablet.AlonRodlBound
import Tablet.RootedTreeCounting
import Tablet.ForwardIndependentTuple
import Tablet.PolarityGraph
import Tablet.ExpanderMixing

open scoped BigOperators LinearAlgebra.Projectivization

set_option maxHeartbeats 2000000

-- [TABLET NODE: DStarMarkedTreeBound]
theorem DStarMarkedTreeBound
    (K : Type) [Field K] [Fintype K]
    (t q k A C : Nat) (ht : 2 ≤ t) (hq : 16 ≤ q)
    (hqpow : ∃ m : Nat, q = 2 ^ m)
    (hK : Fintype.card K = q) :
    let G := PolarityGraph K t ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableEq G.vertex := Classical.decEq _
    letI : DecidableRel G.adj := G.decidableAdj
    ∀ (n d : Nat) (lambda : ℝ),
      (@Fintype.card G.vertex G.fintype = n ∧
        (∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d) ∧
        (∀ x y : G.vertex → ℝ,
          |(∑ u, ∑ v, x u * (if G.adj u v then 1 else 0) * y v) -
              (d : ℝ) / n * (∑ u, x u) * (∑ v, y v)| ≤
            lambda * Real.sqrt ((∑ u, (x u) ^ 2) * (∑ v, (y v) ^ 2))) ∧
        (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
        (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
        lambda ≤ 2 * Real.sqrt d) →
      20000 * t * t * (t + 1) ≤ A →
      2 * t * A ≤ C →
      4 * A ≤ C →
      C ≤ q →
      C * q * (Nat.log 2 q) ^ 2 ≤ k →
      let D : LooplessDigraph := {
        vertex := {p : G.vertex × G.vertex // G.adj p.1 p.2}
        fintype := inferInstance
        arc := fun u v => G.adj u.1.1 v.1.2 ∧ ¬ G.adj v.1.1 u.1.2
        decidableArc := inferInstance
        loopless := by
          intro u hu
          exact hu.2 hu.1
      }
      ∃ count : (Fin k → Bool) → Nat,
        ForwardIndependentCount D k = ∑ z, count z ∧
        (∀ z, count z ≤
          (4 * q ^ (2 * t - 1)) ^
              (∑ i, if z i = true then 1 else 0) *
            (A * q ^ t) ^
              (k - ∑ i, if z i = true then 1 else 0)) ∧
        (∀ z, count z > 0 →
          (∑ i, if z i = true then 1 else 0) ≤
            A * q * Nat.log 2 q) := by
-- BODY
  sorry
