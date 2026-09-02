import Tablet.ForwardIndependentCount
import Tablet.AlonRodlBound
import Tablet.RootedTreeCounting
import Tablet.ForwardIndependentTuple
import Tablet.PolarityGraph
import Tablet.ExpanderMixing
import Tablet.ProjectiveSpanPointBound
import Tablet.OrthogonalComplementCardinality
import Tablet.StrictSpanGrowth
import Tablet.IncidenceDecayBound

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
      letI : Fintype D.vertex := D.fintype
      letI : ∀ m : Nat, Finite (ForwardIndependentTuple D m) := fun m =>
        Finite.of_injective (fun σ : ForwardIndependentTuple D m => σ.vertex) (by
          intro σ τ h
          cases σ
          cases τ
          simp_all)
      let takePrefix : ∀ {m : Nat} (σ : ForwardIndependentTuple D m)
          (r : Nat), r ≤ m → ForwardIndependentTuple D r :=
        fun {m} σ r hr =>
          { vertex := fun i => σ.vertex ⟨i.val, by omega⟩
            independent := by
              intro i j hij
              apply σ.independent
              exact by omega }
      ∃ mark : ∀ m : Nat, ForwardIndependentTuple D m → Bool,
        (∀ σ : ForwardIndependentTuple D 0, mark 0 σ = true) ∧
        (∀ (m : Nat) (σ : ForwardIndependentTuple D m),
          let child : ForwardIndependentTuple D (m + 1) → Prop :=
            fun τ => (∀ i : Fin m, τ.vertex i.castSucc = σ.vertex i)
              ∧ mark (m + 1) τ = true
          Nat.card {τ : ForwardIndependentTuple D (m + 1) // child τ} ≤
            A * q ^ t) ∧
        (∀ (m : Nat) (σ : ForwardIndependentTuple D m),
          (∑ i : Fin m,
            if mark (i.val + 1) (takePrefix σ (i.val + 1) (by omega)) = false
            then 1 else 0) ≤ A * q * Nat.log 2 q) := by
-- BODY
  classical
  have hspan_support :
      ∀ s : Finset (Fin (t + 1) → K),
        Nat.card (Projectivization K
          (Submodule.span K (s : Set (Fin (t + 1) → K)))) ≤
          Fintype.card K ^ s.card := by
    intro s
    exact ProjectiveSpanPointBound K (Fin (t + 1) → K) s
  have horth_support :=
    OrthogonalComplementCardinality (K := K) (V := Fin (t + 1) → K)
  have hgrowth_support :
      ∀ (W : Submodule K (Fin (t + 1) → K)) (v : Fin (t + 1) → K),
        v ∉ W →
          Module.finrank K
              (↑(W ⊔ Submodule.span K ({v} : Set (Fin (t + 1) → K))) : Type) =
            Module.finrank K W + 1 := by
    intro W v hv
    exact StrictSpanGrowth K (Fin (t + 1) → K) W v hv
  have hincidence_support :=
    IncidenceDecayBound (V := Fin (t + 1) → K)
  sorry
