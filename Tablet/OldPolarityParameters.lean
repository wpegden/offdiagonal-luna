import Tablet.OldPairDigraph
import Tablet.NonprincipalSpectralBound
import Tablet.PolarityGraph
import Tablet.ExpanderMixing
import Mathlib.Algebra.IsPrimePow
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

open scoped LinearAlgebra.Projectivization BigOperators
open Matrix

set_option maxHeartbeats 1000000

-- [TABLET NODE: OldPolarityParameters]
theorem OldPolarityParameters
    (K : Type) [Field K] [Fintype K]
    (t q : Nat) (ht : 2 ≤ t) (hqpow : IsPrimePow q) (hq : 16 ≤ q)
    (hK : Fintype.card K = q) :
    let G := PolarityGraph K t ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableRel G.adj := G.decidableAdj
    (∀ (a b : Fin (t + 2) → G.vertex),
      (∀ i, ¬ G.adj (a i) (b i)) →
      (∀ ⦃i j : Fin (t + 2)⦄,
        i.val < j.val → G.adj (a i) (b j)) → False) ∧
    ∃ n d : Nat, ∃ lambda : ℝ,
      @Fintype.card G.vertex G.fintype = n ∧
      n = (q ^ (t + 1) - 1) / (q - 1) ∧
      d = (q ^ t - 1) / (q - 1) ∧
        (∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d) ∧
        lambda = Real.sqrt ((d : ℝ) -
          ((((q ^ (t - 1) - 1) / (q - 1) : Nat) : ℝ))) ∧
        NonprincipalSpectralBound G lambda ∧
      (∀ x y : G.vertex → ℝ,
        |(∑ u, ∑ v, x u * (if G.adj u v then 1 else 0) * y v) -
            (d : ℝ) / n * (∑ u, x u) * (∑ v, y v)| ≤
          lambda * Real.sqrt ((∑ u, (x u) ^ 2) * (∑ v, (y v) ^ 2))) ∧
      (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
      (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
      lambda ≤ 2 * Real.sqrt d ∧
      ((q : ℝ) ^ (2 * t) / 2 ≤
        (@Fintype.card (OldPairDigraph G).vertex
          (OldPairDigraph G).fintype : ℝ)) := by
-- BODY
  classical
  dsimp [PolarityGraph]
  let V := Fin (t + 1) → K
  let P := Projectivization K V
  letI : Fintype P := Fintype.ofFinite P
  let adj : P → P → Prop := Projectivization.orthogonal
  have horth : ∀ (m : Nat) (x : Fin (m + 1) → K) (hx : x ≠ 0),
      Nat.card {u : Projectivization K (Fin (m + 1) → K) //
        Projectivization.orthogonal (Projectivization.mk K x hx) u} =
        (Fintype.card K ^ m - 1) / (Fintype.card K - 1) := by
    intro m x hx
    let f : (Fin (m + 1) → K) →ₗ[K] K :=
      { toFun := fun y => x ⬝ᵥ y
        map_add' := by intro y z; simp [dotProduct_add]
        map_smul' := by intro a y; simp }
    have hf : Function.Surjective f := by
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
      intro z
      refine ⟨Pi.single i (z / x i), ?_⟩
      simpa [f, dotProduct_single, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
        (mul_div_cancel_left₀ z hi)
    have hfin : Module.finrank K (LinearMap.ker f) = m := by
      have hq := f.quotKerEquivRange.finrank_eq
      have hr : Module.finrank K (LinearMap.range f) = 1 := by
        rw [LinearMap.range_eq_top.mpr hf, finrank_top, Module.finrank_self]
      have h := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
      have hV : Module.finrank K (Fin (m + 1) → K) = m + 1 := by simp
      rw [hq, hr] at h
      rw [hV] at h
      omega
    have hcardker : Nat.card (Projectivization K (LinearMap.ker f)) =
        (Fintype.card K ^ m - 1) / (Fintype.card K - 1) := by
      rw [Projectivization.card_of_finrank K (LinearMap.ker f) hfin]
      simp only [Nat.card_eq_fintype_card]
      rw [Nat.geomSum_eq]
      have hK2 := Fintype.one_lt_card (α := K)
      omega
    let phi : Projectivization K (LinearMap.ker f) →
        Projectivization K (Fin (m + 1) → K) :=
      Projectivization.map (Submodule.subtype (LinearMap.ker f))
        (Submodule.subtype_injective (LinearMap.ker f))
    let psi : Projectivization K (LinearMap.ker f) →
        {u : Projectivization K (Fin (m + 1) → K) //
          Projectivization.orthogonal (Projectivization.mk K x hx) u} := fun z =>
      ⟨phi z, by
        change Projectivization.orthogonal (Projectivization.mk K x hx)
          (Projectivization.map (Submodule.subtype (LinearMap.ker f))
            (Submodule.subtype_injective (LinearMap.ker f)) z)
        induction z using Projectivization.ind with
        | h w hw =>
          rw [Projectivization.map_mk]
          apply (Projectivization.orthogonal_mk hx (by
            exact (Submodule.subtype_injective (LinearMap.ker f)).ne hw)).2
          exact w.property⟩
    have hpsi : Function.Bijective psi := by
      constructor
      · intro z z' hzz'
        apply Projectivization.map_injective (Submodule.subtype (LinearMap.ker f))
          (Submodule.subtype_injective (LinearMap.ker f))
        exact congrArg Subtype.val hzz'
      · intro u
        let y := u.1.rep
        have hy : y ≠ 0 := u.1.rep_nonzero
        have hxy : x ⬝ᵥ y = 0 := by
          apply (Projectivization.orthogonal_mk hx hy).mp
          simpa [y] using u.2
        have hyker : y ∈ LinearMap.ker f := hxy
        let z : Projectivization K (LinearMap.ker f) :=
          Projectivization.mk K ⟨y, hyker⟩ (by
            intro h
            exact hy (congrArg Subtype.val h))
        refine ⟨z, ?_⟩
        apply Subtype.ext
        change Projectivization.map (Submodule.subtype (LinearMap.ker f))
          (Submodule.subtype_injective (LinearMap.ker f)) z = u.1
        rw [Projectivization.map_mk]
        exact Projectivization.mk_rep u.1
    have hcard := Nat.card_congr (Equiv.ofBijective psi hpsi)
    rw [← hcard]
    simpa [phi] using hcardker
  have hpair : ∀ (m : Nat) (x z : Fin (m + 1) → K)
      (hx : x ≠ 0) (hz : z ≠ 0)
      (hproj : Projectivization.mk K x hx ≠ Projectivization.mk K z hz),
      Nat.card {u : Projectivization K (Fin (m + 1) → K) //
        Projectivization.orthogonal (Projectivization.mk K x hx) u ∧
          Projectivization.orthogonal (Projectivization.mk K z hz) u} =
        (Fintype.card K ^ (m - 1) - 1) / (Fintype.card K - 1) := by
    intro m x z hx hz hproj
    let V' := Fin (m + 1) → K
    let B : LinearMap.BilinForm K V' := dotProductBilin K K
    have hB : B.Nondegenerate := by
      refine ⟨?_, ?_⟩
      · intro v hv
        apply (dotProduct_eq_zero_iff.mp ?_)
        intro w
        have h := hv w
        dsimp [B, dotProductBilin] at h
        simpa [dotProduct_comm] using h
      · intro v hv
        apply (dotProduct_eq_zero_iff.mp ?_)
        intro w
        have h := hv w
        dsimp [B, dotProductBilin] at h
        simpa [dotProduct_comm] using h
    have hBs : B.IsSymm := by
      rw [LinearMap.BilinForm.isSymm_def]
      intro u v
      simpa [B, dotProductBilin] using (dotProduct_comm u v)
    have hlin : LinearIndependent K (fun i : Fin 2 => (![x, z] i)) := by
      rw [LinearIndependent.pair_iff]
      intro aa c hac
      constructor
      · by_contra haa
        have hc : c ≠ 0 := by
          intro hc
          exact haa ((smul_eq_zero.mp (by simpa [hc] using hac)).resolve_right hx)
        have ha : aa ≠ 0 := by
          intro haa
          have hcz : c • z = 0 := by simpa [haa] using hac
          exact hz ((smul_eq_zero.mp hcz).resolve_left hc)
        have hrel : aa • x = -(c • z) := eq_neg_of_add_eq_zero_left hac
        have hzx : x = (-(aa⁻¹ * c)) • z := by
          calc
            x = aa⁻¹ • aa • x := (inv_smul_smul₀ ha x).symm
            _ = aa⁻¹ • (-(c • z)) := by rw [hrel]
            _ = (-(aa⁻¹ * c)) • z := by simp [smul_smul]
        apply hproj
        let r : Kˣ := Units.mk0 (-(aa⁻¹ * c)) (by
          intro hr
          apply hx
          simpa [hr] using hzx)
        apply (Projectivization.mk_eq_mk_iff K x z hx hz).2
        refine ⟨r, ?_⟩
        simpa [r] using hzx.symm
      · by_contra hc
        have ha : aa ≠ 0 := by
          intro haa
          have hcz : c • z = 0 := by simpa [haa] using hac
          exact hc ((smul_eq_zero.mp hcz).resolve_right hz)
        have hc' : c ≠ 0 := by
          intro hcc
          have hax : aa • x = 0 := by simpa [hcc] using hac
          exact ha ((smul_eq_zero.mp hax).resolve_right hx)
        have hrel : c • z = -(aa • x) := eq_neg_of_add_eq_zero_right hac
        have hzx : z = (-(c⁻¹ * aa)) • x := by
          calc
            z = c⁻¹ • c • z := (inv_smul_smul₀ hc' z).symm
            _ = c⁻¹ • (-(aa • x)) := by rw [hrel]
            _ = (-(c⁻¹ * aa)) • x := by simp [smul_smul]
        apply hproj
        let r : Kˣ := Units.mk0 (-(c⁻¹ * aa)) (by
          intro hr
          apply hz
          simpa [hr] using hzx)
        exact ((Projectivization.mk_eq_mk_iff K z x hz hx).2 (by
          refine ⟨r, ?_⟩
          simpa [r] using hzx.symm)).symm
    let W : Submodule K V' := Submodule.span K {x, z}
    have hW : Module.finrank K W = 2 := by
      have hh := finrank_span_eq_card (R := K) (M := V') hlin
      have hrange : Set.range (fun i : Fin 2 => (![x, z] i)) = ({x, z} : Set V') := by
        ext v
        simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hv
          rcases hv with rfl | rfl
          · exact ⟨0, rfl⟩
          · exact ⟨1, rfl⟩
      rw [hrange] at hh
      exact hh
    have hO : Module.finrank K (B.orthogonal W) = m - 1 := by
      rw [LinearMap.BilinForm.finrank_orthogonal hB W]
      simp [V', hW]
    have hcardS : Nat.card (Projectivization K (B.orthogonal W)) =
        (Fintype.card K ^ (m - 1) - 1) / (Fintype.card K - 1) := by
      rw [Projectivization.card_of_finrank K (B.orthogonal W) hO]
      simp only [Nat.card_eq_fintype_card]
      rw [Nat.geomSum_eq]
      have hK2 := Fintype.one_lt_card (α := K)
      omega
    let S : Submodule K V' := B.orthogonal W
    let phi : Projectivization K S → Projectivization K V' :=
      Projectivization.map (Submodule.subtype S) S.subtype_injective
    let psi : Projectivization K S →
        {u : Projectivization K V' //
          Projectivization.orthogonal (Projectivization.mk K x hx) u ∧
            Projectivization.orthogonal (Projectivization.mk K z hz) u} := fun v =>
      ⟨phi v, by
        change Projectivization.orthogonal (Projectivization.mk K x hx)
            (Projectivization.map (Submodule.subtype S) S.subtype_injective v) ∧
          Projectivization.orthogonal (Projectivization.mk K z hz)
            (Projectivization.map (Submodule.subtype S) S.subtype_injective v)
        induction v using Projectivization.ind with
        | h w hw =>
          rw [Projectivization.map_mk]
          constructor
          · apply (Projectivization.orthogonal_mk hx (by exact S.subtype_injective.ne hw)).2
            have hh := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.property) x
              (Submodule.subset_span (by simp))
            simpa [B, dotProductBilin] using hh
          · apply (Projectivization.orthogonal_mk hz (by exact S.subtype_injective.ne hw)).2
            have hh := (LinearMap.BilinForm.mem_orthogonal_iff.mp w.property) z
              (Submodule.subset_span (by simp))
            simpa [B, dotProductBilin] using hh⟩
    have hpsi : Function.Bijective psi := by
      constructor
      · intro v v' hv
        apply Projectivization.map_injective (Submodule.subtype S) S.subtype_injective
        exact congrArg Subtype.val hv
      · intro u
        let y := u.1.rep
        have hy : y ≠ 0 := u.1.rep_nonzero
        have hxy : x ⬝ᵥ y = 0 := by
          apply (Projectivization.orthogonal_mk hx hy).mp
          simpa [y] using u.2.1
        have hzy : z ⬝ᵥ y = 0 := by
          apply (Projectivization.orthogonal_mk hz hy).mp
          simpa [y] using u.2.2
        have hyS : y ∈ S := by
          apply LinearMap.BilinForm.mem_orthogonal_iff.mpr
          intro w hw
          rcases Submodule.mem_span_pair.mp hw with ⟨aa, c, hab⟩
          rw [← hab]
          simp only [map_add, map_smul]
          simp [B, dotProductBilin, hxy, hzy]
        let v : Projectivization K S := Projectivization.mk K ⟨y, hyS⟩ (by
          intro h
          exact hy (congrArg Subtype.val h))
        refine ⟨v, ?_⟩
        apply Subtype.ext
        change Projectivization.map (Submodule.subtype S) S.subtype_injective v = u.1
        rw [Projectivization.map_mk]
        exact Projectivization.mk_rep u.1
    have hcard := Nat.card_congr (Equiv.ofBijective psi hpsi)
    rw [← hcard]
    simpa [S] using hcardS
  have hsquare_zero :
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (r : W → W → Prop) [DecidableRel r],
        (∀ u v, r u v ↔ r v u) →
        (d0 a0 : Nat) → a0 ≤ d0 →
        (hcount0 : ∀ u v, Fintype.card {w : W // r u w ∧ r w v} =
          if u = v then d0 else a0) →
        (f : W → ℝ) → (∑ w, f w = 0) → (v : W) →
        (∑ u, if r v u then (∑ w, if r u w then f w else 0) else 0) =
          (d0 - a0 : ℝ) * f v := by
    intro W _ _ r _ hsym d0 a0 ha0 hcount0 f hzero v
    have hrewrite (u w : W) :
        (if r v u then (if r u w then f w else 0) else 0) =
          (if r v u ∧ r u w then (1 : ℝ) else 0) * f w := by
      by_cases h1 : r v u <;> by_cases h2 : r u w <;> simp [h1, h2]
    have hsum (w : W) :
        (∑ u, if r v u ∧ r u w then (1 : ℝ) else 0) =
          (Fintype.card {u : W // r v u ∧ r u w} : ℝ) := by
      rw [Finset.sum_boole, Fintype.card_subtype]
    calc
      (∑ u, if r v u then (∑ w, if r u w then f w else 0) else 0) =
          ∑ u, ∑ w, (if r v u then (if r u w then f w else 0) else 0) := by
            apply Finset.sum_congr rfl
            intro u hu
            by_cases h : r v u <;> simp [h]
      _ = ∑ w, ∑ u, (if r v u then (if r u w then f w else 0) else 0) := by
            rw [Finset.sum_comm]
      _ = ∑ w, (Fintype.card {u : W // r v u ∧ r u w} : ℝ) * f w := by
            apply Finset.sum_congr rfl
            intro w hw
            simp_rw [hrewrite]
            rw [← Finset.sum_mul]
            rw [hsum]
      _ = ∑ w, (if v = w then (d0 : ℝ) else a0) * f w := by
            apply Finset.sum_congr rfl
            intro w hw
            rw [hcount0]
            by_cases h : v = w <;> simp [h]
      _ = (a0 : ℝ) * (∑ w, f w) + (d0 - a0 : ℝ) * f v := by
            have hp (w : W) :
                (if v = w then (d0 : ℝ) else a0) * f w =
                  (a0 : ℝ) * f w +
                    (if v = w then (d0 - a0 : ℝ) * f w else 0) := by
              by_cases h : v = w <;> simp [h]
              ring
            rw [show (∑ w, (if v = w then (d0 : ℝ) else a0) * f w) =
                ∑ w, ((a0 : ℝ) * f w +
                  (if v = w then (d0 - a0 : ℝ) * f w else 0)) by
              apply Finset.sum_congr rfl
              intro w hw
              exact hp w]
            rw [Finset.sum_add_distrib]
            simp_rw [← Finset.mul_sum]
            simp
      _ = (d0 - a0 : ℝ) * f v := by simp [hzero]
  have hnonprincipal_generic :
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (r : W → W → Prop) [DecidableRel r],
        (hsym0 : ∀ u v, r u v ↔ r v u) →
        (d0 a0 : Nat) → a0 ≤ d0 →
        (hcount0 : ∀ u v, Fintype.card {w : W // r u w ∧ r w v} =
          if u = v then d0 else a0) →
        (hda0 : 0 ≤ (d0 : ℝ) - a0) →
        NonprincipalSpectralBound
          { vertex := W, fintype := inferInstance, adj := r,
            decidableAdj := inferInstance, symmetric := by
              intro u v
              exact hsym0 u v }
          (Real.sqrt ((d0 : ℝ) - a0)) := by
    intro W _ _ r _ hsym d0 a0 ha0 hcount0 hda0
    intro mu v hv hzero heig
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hv
    have hsq := hsquare_zero r hsym d0 a0 ha0 hcount0 v hzero i
    have heig_sq :
        (∑ u, if r i u then (∑ w, if r u w then v w else 0) else 0) =
          mu ^ 2 * v i := by
      calc
        (∑ u, if r i u then (∑ w, if r u w then v w else 0) else 0) =
            ∑ u, if r i u then mu * v u else 0 := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases h : r i u <;> simp [h, heig u]
        _ = ∑ u, mu * (if r i u then v u else 0) := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases h : r i u <;> simp [h]
        _ = mu * (∑ u, if r i u then v u else 0) := by
              rw [Finset.mul_sum]
        _ = mu * (mu * v i) := by rw [heig i]
        _ = mu ^ 2 * v i := by ring
    have hmul : (mu ^ 2 - ((d0 : ℝ) - a0)) * v i = 0 := by
      rw [sub_mul]
      rw [← heig_sq, ← hsq]
      ring
    have hmu : mu ^ 2 = (d0 : ℝ) - a0 := by
      have h := (mul_eq_zero.mp hmul).resolve_right hi
      linarith
    have hsqrt : Real.sqrt ((d0 : ℝ) - a0) ^ 2 = (d0 : ℝ) - a0 :=
      Real.sq_sqrt hda0
    have habs : |mu| ^ 2 = Real.sqrt ((d0 : ℝ) - a0) ^ 2 := by
      rw [sq_abs, hmu, hsqrt]
    nlinarith [abs_nonneg mu, Real.sqrt_nonneg ((d0 : ℝ) - a0)]
  have hbilinear_generic :
      ∀ {W : Type} [Fintype W] [DecidableEq W]
        (r : W → W → Prop) [DecidableRel r],
        (∀ u v, r u v ↔ r v u) →
        (n0 d0 a0 : Nat) → 0 < n0 → Fintype.card W = n0 →
        (hdeg0 : ∀ u, Fintype.card {v : W // r u v} = d0) →
        a0 ≤ d0 →
        (hcount0 : ∀ u v, Fintype.card {w : W // r u w ∧ r w v} =
          if u = v then d0 else a0) →
        0 ≤ (d0 : ℝ) - a0 →
        ∀ x y : W → ℝ,
          |(∑ u, ∑ v, x u * (if r u v then 1 else 0) * y v) -
              (d0 : ℝ) / n0 * (∑ u, x u) * (∑ v, y v)| ≤
            Real.sqrt ((d0 : ℝ) - a0) *
              Real.sqrt ((∑ u, (x u) ^ 2) * (∑ v, (y v) ^ 2)) := by
    intro W _ _ r _ hsym n0 d0 a0 hn0 hcard0 hdeg0 ha0 hcount0 hda0 x y
    have hrow (u : W) : (∑ v, if r u v then (1 : ℝ) else 0) = d0 := by
      rw [Finset.sum_boole]
      have hd := hdeg0 u
      rw [Fintype.card_subtype] at hd
      exact_mod_cast hd
    have hcol (v : W) : (∑ u, if r u v then (1 : ℝ) else 0) = d0 := by
      calc
        (∑ u, if r u v then (1 : ℝ) else 0) =
            ∑ u, if r v u then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro u hu
              by_cases h : r u v
              · have h' := (hsym u v).mp h
                simp [h, h']
              · have h' := (hsym u v).not.mp h
                simp [h, h']
        _ = d0 := hrow v
    have hbilin_symm (f g : W → ℝ) :
        (∑ u, f u * (∑ v, if r u v then g v else 0)) =
          (∑ u, g u * (∑ v, if r u v then f v else 0)) := by
      calc
        (∑ u, f u * (∑ v, if r u v then g v else 0)) =
            ∑ u, ∑ v, f u * (if r u v then g v else 0) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [Finset.mul_sum]
        _ = ∑ v, ∑ u, g v * (if r v u then f u else 0) := by
              rw [Finset.sum_comm]
              apply Finset.sum_congr rfl
              intro v hv
              apply Finset.sum_congr rfl
              intro u hu
              by_cases h : r u v
              · have h' := (hsym u v).mp h
                simp [h, h', mul_comm]
              · have h' := (hsym u v).not.mp h
                simp [h, h', mul_comm]
        _ = ∑ v, g v * (∑ u, if r v u then f u else 0) := by
              apply Finset.sum_congr rfl
              intro v hv
              rw [Finset.mul_sum]
    let sx : ℝ := ∑ u, x u
    let sy : ℝ := ∑ u, y u
    let x0 : W → ℝ := fun u => x u - sx / n0
    let y0 : W → ℝ := fun u => y u - sy / n0
    have hsumx0 : ∑ u, x0 u = 0 := by
      simp only [x0]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, hcard0]
      dsimp [sx]
      simp only [nsmul_eq_mul]
      field_simp
      ring
    have hsumy0 : ∑ u, y0 u = 0 := by
      simp only [y0]
      rw [Finset.sum_sub_distrib]
      simp only [Finset.sum_const, Finset.card_univ, hcard0]
      dsimp [sy]
      simp only [nsmul_eq_mul]
      field_simp
      ring
    have hcenter :
        (∑ u, ∑ v, x u * (if r u v then 1 else 0) * y v) -
            (d0 : ℝ) / n0 * (∑ u, x u) * (∑ v, y v) =
          ∑ u, x0 u * (∑ v, if r u v then y0 v else 0) := by
      have hleft :
          (∑ u, ∑ v, x u * (if r u v then 1 else 0) * y v) =
            ∑ u, x u * (∑ v, if r u v then y v else 0) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro v hv
        by_cases h : r u v <;> simp [h]
      have hsumA :
          (∑ u, ∑ v, if r u v then y v else 0) = (d0 : ℝ) * sy := by
        rw [Finset.sum_comm]
        calc
          (∑ v, ∑ u, if r u v then y v else 0) =
              ∑ v, (∑ u, if r u v then 1 else 0) * y v := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [Finset.sum_mul]
                apply Finset.sum_congr rfl
                intro u hu
                by_cases h : r u v <;> simp [h]
          _ = ∑ v, (d0 : ℝ) * y v := by
                apply Finset.sum_congr rfl
                intro v hv
                rw [hcol]
          _ = (d0 : ℝ) * sy := by
                dsimp [sy]
                rw [Finset.mul_sum]
      have hycenter (u : W) :
          (∑ v, if r u v then y0 v else 0) =
            (∑ v, if r u v then y v else 0) - (d0 : ℝ) * sy / n0 := by
        calc
          (∑ v, if r u v then y0 v else 0) =
              ∑ v, ((if r u v then y v else 0) -
                (if r u v then (1 : ℝ) else 0) * (sy / n0)) := by
                  apply Finset.sum_congr rfl
                  intro v hv
                  by_cases h : r u v <;> simp [y0, h]
          _ = (∑ v, if r u v then y v else 0) -
                (∑ v, if r u v then (1 : ℝ) else 0) * (sy / n0) := by
                  rw [Finset.sum_sub_distrib, Finset.sum_mul]
          _ = (∑ v, if r u v then y v else 0) - (d0 : ℝ) * sy / n0 := by
                  rw [hrow]
                  ring
      have halg :
          (∑ u, (x u - sx / n0) *
            ((∑ v, if r u v then y v else 0) - (d0 : ℝ) * sy / n0)) =
            (∑ u, x u * (∑ v, if r u v then y v else 0)) -
              (d0 : ℝ) / n0 * sx * sy := by
        calc
          (∑ u, (x u - sx / n0) *
              ((∑ v, if r u v then y v else 0) - (d0 : ℝ) * sy / n0)) =
              ∑ u, (x u * (∑ v, if r u v then y v else 0) -
                x u * ((d0 : ℝ) * sy / n0) -
                (sx / n0) * (∑ v, if r u v then y v else 0) +
                (sx / n0) * ((d0 : ℝ) * sy / n0)) := by
                  apply Finset.sum_congr rfl
                  intro u hu
                  ring
          _ = (∑ u, x u * (∑ v, if r u v then y v else 0)) -
                (∑ u, x u * ((d0 : ℝ) * sy / n0)) -
                (∑ u, (sx / n0) * (∑ v, if r u v then y v else 0)) +
                (∑ u, (sx / n0) * ((d0 : ℝ) * sy / n0)) := by
                  simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
                  ring
          _ = (∑ u, x u * (∑ v, if r u v then y v else 0)) -
                sx * ((d0 : ℝ) * sy / n0) -
                (sx / n0) * ((d0 : ℝ) * sy) +
                (n0 : ℝ) * (sx / n0) * ((d0 : ℝ) * sy / n0) := by
                  have h1 :
                      (∑ u, x u * ((d0 : ℝ) * sy / n0)) =
                        sx * ((d0 : ℝ) * sy / n0) := by
                    dsimp [sx]
                    rw [Finset.sum_mul]
                  have h2 :
                      (∑ u, (sx / n0) * (∑ v, if r u v then y v else 0)) =
                        (sx / n0) * ((d0 : ℝ) * sy) := by
                    rw [← Finset.mul_sum, hsumA]
                  have h3 :
                      (∑ u : W, (sx / n0) * ((d0 : ℝ) * sy / n0)) =
                        (n0 : ℝ) * (sx / n0) * ((d0 : ℝ) * sy / n0) := by
                    simp only [Finset.sum_const, Finset.card_univ, hcard0,
                      nsmul_eq_mul]
                    ring
                  rw [h1, h2, h3]
          _ = (∑ u, x u * (∑ v, if r u v then y v else 0)) -
                (d0 : ℝ) / n0 * sx * sy := by
                  field_simp [hn0.ne']
                  ring
      rw [hleft]
      calc
        (∑ u, x u * (∑ v, if r u v then y v else 0)) -
            (d0 : ℝ) / n0 * sx * sy =
          ∑ u, (x u - sx / n0) *
            ((∑ v, if r u v then y v else 0) - (d0 : ℝ) * sy / n0) :=
              halg.symm
        _ = ∑ u, x0 u * (∑ v, if r u v then y0 v else 0) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [hycenter]
    have henergy (f : W → ℝ) (hf : ∑ u, f u = 0) :
        ∑ u, (∑ v, if r u v then f v else 0) ^ 2 =
          ((d0 : ℝ) - a0) * ∑ v, f v ^ 2 := by
      let Af : W → ℝ := fun u => ∑ v, if r u v then f v else 0
      have hsq (u : W) :
          (∑ v, if r u v then Af v else 0) = ((d0 : ℝ) - a0) * f u := by
        dsimp [Af]
        exact hsquare_zero r hsym d0 a0 ha0 hcount0 f hf u
      calc
        (∑ u, (∑ v, if r u v then f v else 0) ^ 2) =
            ∑ u, Af u * Af u := by
              apply Finset.sum_congr rfl
              intro u hu
              dsimp [Af]
              ring
        _ = ∑ u, f u * (∑ v, if r u v then Af v else 0) := by
              exact (hbilin_symm f Af).symm
        _ = ∑ u, f u * (((d0 : ℝ) - a0) * f u) := by
              apply Finset.sum_congr rfl
              intro u hu
              rw [hsq]
        _ = ((d0 : ℝ) - a0) * ∑ u, f u ^ 2 := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u hu
              ring
    have hsqrt :
        Real.sqrt (((d0 : ℝ) - a0) * (∑ u, x0 u ^ 2) *
          (∑ v, y0 v ^ 2)) =
        Real.sqrt ((d0 : ℝ) - a0) *
          Real.sqrt ((∑ u, x0 u ^ 2) * (∑ v, y0 v ^ 2)) := by
      rw [show (((d0 : ℝ) - a0) * (∑ u, x0 u ^ 2) * (∑ v, y0 v ^ 2)) =
          ((d0 : ℝ) - a0) * ((∑ u, x0 u ^ 2) * (∑ v, y0 v ^ 2)) by ring]
      rw [Real.sqrt_mul hda0]
    have hvariance (f : W → ℝ) (sf : ℝ) (f0 : W → ℝ)
        (hsf : sf = ∑ u, f u) (hf0 : ∀ u, f0 u = f u - sf / n0) :
        ∑ u, f0 u ^ 2 = (∑ u, f u ^ 2) - sf ^ 2 / n0 := by
      have h1 :
          (∑ u, f0 u ^ 2) =
            ∑ u, (f u ^ 2 - 2 * f u * (sf / n0) + (sf / n0) ^ 2) := by
        apply Finset.sum_congr rfl
        intro u hu
        rw [hf0 u]
        ring
      rw [h1]
      simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib]
      have h2 : (∑ u, 2 * f u * (sf / n0)) = 2 * sf * (sf / n0) := by
        rw [← Finset.sum_mul]
        rw [← Finset.mul_sum, hsf]
      have h3 : (∑ u : W, (sf / n0) ^ 2) =
          (n0 : ℝ) * (sf / n0) ^ 2 := by
        simp only [Finset.sum_const, Finset.card_univ, hcard0, nsmul_eq_mul]
      rw [h2, h3]
      field_simp [hn0.ne']
      ring
    have hxvar := hvariance x sx x0 rfl (by intro u; rfl)
    have hyvar := hvariance y sy y0 rfl (by intro u; rfl)
    have hxnonneg : 0 ≤ ∑ u, x0 u ^ 2 :=
      Finset.sum_nonneg (fun u _ => sq_nonneg _)
    have hynonneg : 0 ≤ ∑ u, y0 u ^ 2 :=
      Finset.sum_nonneg (fun u _ => sq_nonneg _)
    have hxall : 0 ≤ ∑ u, x u ^ 2 :=
      Finset.sum_nonneg (fun u _ => sq_nonneg _)
    have hyall : 0 ≤ ∑ u, y u ^ 2 :=
      Finset.sum_nonneg (fun u _ => sq_nonneg _)
    have hxle : (∑ u, x0 u ^ 2) ≤ ∑ u, x u ^ 2 := by
      rw [hxvar]
      have h : 0 ≤ sx ^ 2 / n0 := div_nonneg (sq_nonneg _) (by positivity)
      linarith
    have hyle : (∑ u, y0 u ^ 2) ≤ ∑ u, y u ^ 2 := by
      rw [hyvar]
      have h : 0 ≤ sy ^ 2 / n0 := div_nonneg (sq_nonneg _) (by positivity)
      linarith
    have hprod :
        (∑ u, x0 u ^ 2) * (∑ u, y0 u ^ 2) ≤
          (∑ u, x u ^ 2) * (∑ u, y u ^ 2) := by
      have h1 : 0 ≤ (∑ u, x u ^ 2) - ∑ u, x0 u ^ 2 := sub_nonneg.mpr hxle
      have h2 : 0 ≤ (∑ u, y u ^ 2) - ∑ u, y0 u ^ 2 := sub_nonneg.mpr hyle
      have h3 : 0 ≤ (∑ u, x0 u ^ 2) *
          ((∑ u, y u ^ 2) - ∑ u, y0 u ^ 2) := mul_nonneg hxnonneg h2
      have h4 : 0 ≤ ((∑ u, x u ^ 2) - ∑ u, x0 u ^ 2) *
          (∑ u, y u ^ 2) := mul_nonneg h1 hyall
      nlinarith
    have hTbound :
        (∑ u, x0 u * (∑ v, if r u v then y0 v else 0)) ^ 2 ≤
          ((d0 : ℝ) - a0) *
            ((∑ u, x0 u ^ 2) * (∑ v, y0 v ^ 2)) := by
      have hc := Finset.sum_mul_sq_le_sq_mul_sq (s := (Finset.univ : Finset W))
        x0 (fun u => ∑ v, if r u v then y0 v else 0)
      have he := henergy y0 hsumy0
      simpa [mul_assoc, mul_left_comm, mul_comm] using
        (hc.trans_eq (by rw [he]; ring))
    rw [hcenter]
    have hRnonneg : 0 ≤ Real.sqrt ((d0 : ℝ) - a0) *
        Real.sqrt ((∑ u, x u ^ 2) * (∑ v, y v ^ 2)) :=
      mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    have hR_sq :
        (Real.sqrt ((d0 : ℝ) - a0) *
          Real.sqrt ((∑ u, x u ^ 2) * (∑ v, y v ^ 2))) ^ 2 =
        ((d0 : ℝ) - a0) *
          ((∑ u, x u ^ 2) * (∑ v, y v ^ 2)) := by
      rw [mul_pow, Real.sq_sqrt hda0,
        Real.sq_sqrt (mul_nonneg hxall hyall)]
    have hsqbound :
        (∑ u, x0 u * (∑ v, if r u v then y0 v else 0)) ^ 2 ≤
        (Real.sqrt ((d0 : ℝ) - a0) *
          Real.sqrt ((∑ u, x u ^ 2) * (∑ v, y v ^ 2))) ^ 2 := by
      exact hTbound.trans (by
        rw [hR_sq]
        exact mul_le_mul_of_nonneg_left hprod hda0)
    nlinarith [sq_abs (∑ u, x0 u *
      (∑ v, if r u v then y0 v else 0))]
  have hcardV : Fintype.card V = q ^ (t + 1) := by
    simp [V, Fintype.card_fun, hK]
  have hnform : Fintype.card P = (q ^ (t + 1) - 1) / (q - 1) := by
    rw [show Fintype.card P = Nat.card P by simp]
    rw [Projectivization.card'']
    simp [P, V, Nat.card_eq_fintype_card, Fintype.card_fun, hK]
  let n : Nat := (q ^ (t + 1) - 1) / (q - 1)
  let d : Nat := (q ^ t - 1) / (q - 1)
  let a0 : Nat := (q ^ (t - 1) - 1) / (q - 1)
  have hPn : Fintype.card P = n := by simpa [n] using hnform
  have hq2 : 2 ≤ q := by omega
  have hqm1 : 0 < q - 1 := by omega
  have hqpos : 0 < q := by omega
  have ht1 : 1 ≤ t - 1 := by omega
  have hpow_mono : q ^ (t - 1) ≤ q ^ t :=
    Nat.pow_le_pow_right hqpos (by omega)
  have hle : a0 ≤ d := by
    dsimp [a0, d]
    exact Nat.div_le_div_right (Nat.sub_le_sub_right hpow_mono 1)
  have hden : q - 1 ≤ q ^ (t + 1) - 1 := by
    have hpow : q ≤ q ^ (t + 1) := Nat.le_pow (by omega)
    exact Nat.sub_le_sub_right hpow 1
  have hdegree : ∀ v : P, Fintype.card {u : P // adj v u} = d := by
    intro v
    have hv : v.rep ≠ 0 := v.rep_nonzero
    have h := horth t v.rep hv
    simpa [adj, d, Nat.card_eq_fintype_card, hK] using h
  have hcount : ∀ u v : P, Fintype.card {w : P // adj u w ∧ adj w v} =
      if u = v then d else a0 := by
    intro u v
    by_cases huv : u = v
    · subst v
      let e : {w : P // adj u w ∧ adj w u} ≃ {w : P // adj u w} :=
        { toFun := fun w => ⟨w.1, w.2.1⟩
          invFun := fun w => ⟨w.1, ⟨w.2, (Projectivization.orthogonal_comm).mpr w.2⟩⟩
          left_inv := by intro w; rfl
          right_inv := by intro w; rfl }
      rw [if_pos rfl, Fintype.card_congr e]
      exact hdegree u
    · have hu : u.rep ≠ 0 := u.rep_nonzero
      have hv : v.rep ≠ 0 := v.rep_nonzero
      have hproj : Projectivization.mk K u.rep hu ≠
          Projectivization.mk K v.rep hv := by
        simpa [Projectivization.mk_rep] using huv
      have h := hpair t u.rep v.rep hu hv hproj
      have hcard := @h
      simpa [adj, a0, Nat.card_eq_fintype_card,
        Projectivization.mk_rep, Projectivization.orthogonal_comm, huv, hK] using hcard
  have hnonneg : 0 ≤ (d : ℝ) - a0 := by
    have hnat : 0 ≤ d - a0 := by omega
    exact_mod_cast hnat
  have hnp : NonprincipalSpectralBound
      { vertex := P, fintype := inferInstance, adj := adj,
        decidableAdj := inferInstance, symmetric := by
          intro u v; exact Projectivization.orthogonal_comm }
      (Real.sqrt ((d : ℝ) - a0)) := by
    exact hnonprincipal_generic adj
      (fun u v => Projectivization.orthogonal_comm) d a0 hle hcount hnonneg
  have hbil : ∀ x y : P → ℝ,
      |(∑ u, ∑ v, x u * (if adj u v then 1 else 0) * y v) -
          (d : ℝ) / n * (∑ u, x u) * (∑ v, y v)| ≤
        Real.sqrt ((d : ℝ) - a0) *
          Real.sqrt ((∑ u, (x u) ^ 2) * (∑ v, (y v) ^ 2)) := by
    exact hbilinear_generic adj
      (fun u v => Projectivization.orthogonal_comm) n d a0
      (by dsimp [n]; exact Nat.div_pos hden hqm1) hnform hdegree
      hle hcount hnonneg
  have htri : ∀ (aa bb : Fin (t + 2) → P),
      (∀ i, ¬ adj (aa i) (bb i)) →
      (∀ ⦃i j : Fin (t + 2)⦄, i.val < j.val → adj (aa i) (bb j)) → False := by
    intro aa bb hdiag hupper
    let V' := Fin (t + 1) → K
    let x : Fin (t + 2) → V' := fun i => (aa i).rep
    let y : Fin (t + 2) → V' := fun i => (bb i).rep
    have hx (i) : x i ≠ 0 := (aa i).rep_nonzero
    have hy (i) : y i ≠ 0 := (bb i).rep_nonzero
    have hlin : LinearIndependent K y := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      by_contra hnot
      let S : Finset (Fin (t + 2)) := Finset.univ.filter (fun i => c i ≠ 0)
      have hS : S.Nonempty := by
        by_contra hS
        apply hnot
        intro i
        by_contra hci
        apply hS
        exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hci⟩⟩
      let i : Fin (t + 2) := S.min' hS
      have hiS : i ∈ S := S.min'_mem hS
      have hci : c i ≠ 0 := (Finset.mem_filter.mp hiS).2
      have hbelow (j : Fin (t + 2)) (hji : j.val < i.val) : c j = 0 := by
        by_contra hcj
        have hjS : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcj⟩
        have hmin' := Finset.min'_le S j hjS
        have hmin : i.val ≤ j.val := by simpa [i] using hmin'
        omega
      have hdot : x i ⬝ᵥ (∑ j, c j • y j) = x i ⬝ᵥ (0 : V') :=
        congrArg (fun z : V' => x i ⬝ᵥ z) hc
      have hdot' : ∑ j, c j * (x i ⬝ᵥ y j) = 0 := by
        calc
          (∑ j, c j * (x i ⬝ᵥ y j)) =
              ∑ j, x i ⬝ᵥ (c j • y j) := by
                apply Finset.sum_congr rfl
                intro j hj
                rw [dotProduct_smul]
                rfl
          _ = x i ⬝ᵥ (∑ j, c j • y j) :=
                (dotProduct_sum (x i) (Finset.univ) (fun j => c j • y j)).symm
          _ = 0 := by rw [hc]; simp
      have hsum : ∑ j, c j * (x i ⬝ᵥ y j) =
          c i * (x i ⬝ᵥ y i) := by
        rw [Finset.sum_eq_single i]
        intro j hj hji
        rcases lt_or_gt_of_ne hji with hlt | hgt
        · rw [hbelow j hlt, zero_mul]
        · have hadj := hupper hgt
          have hzero : x i ⬝ᵥ y j = 0 := by
            apply (Projectivization.orthogonal_mk (hx i) (hy j)).mp
            simpa [x, y, adj] using hadj
          rw [hzero, mul_zero]
        simp
      have hdiag' : x i ⬝ᵥ y i ≠ 0 := by
        intro hzero
        apply hdiag i
        rw [← (aa i).mk_rep, ← (bb i).mk_rep]
        apply (Projectivization.orthogonal_mk (hx i) (hy i)).mpr
        simpa [x, y, adj] using hzero
      have : c i * (x i ⬝ᵥ y i) = 0 := by rw [← hsum, hdot']
      exact hci ((mul_eq_zero.mp this).resolve_right hdiag')
    have hcard := LinearIndependent.fintype_card_le_finrank hlin
    have hdim : Module.finrank K V' = t + 1 := by simp [V']
    rw [hdim] at hcard
    simpa using hcard
  have hapos : 0 ≤ (a0 : ℝ) := by positivity
  have hdp : 0 ≤ (d : ℝ) := by positivity
  have hlam : Real.sqrt ((d : ℝ) - a0) ≤ 2 * Real.sqrt d := by
    have h₁ : Real.sqrt ((d : ℝ) - a0) ≤ Real.sqrt d := by
      apply Real.sqrt_le_sqrt
      linarith
    have h₂ : 0 ≤ Real.sqrt d := Real.sqrt_nonneg _
    linarith
  have hnp' : NonprincipalSpectralBound
      { vertex := P, fintype := inferInstance, adj := adj,
        decidableAdj := inferInstance, symmetric := by
          intro u v; exact Projectivization.orthogonal_comm }
      (Real.sqrt ((d : ℝ) - a0)) := hnp
  refine ⟨?_, n, d, Real.sqrt ((d : ℝ) - a0), ?_⟩
  · intro aa bb hdiag hupper
    exact htri aa bb hdiag hupper
  constructor
  · simpa [n] using hnform
  constructor
  · rfl
  constructor
  · rfl
  constructor
  · exact hdegree
  constructor
  · rfl
  constructor
  · simpa [P, adj] using hnp'
  constructor
  · simpa [P, adj] using hbil
  have hnsub : n - d = q ^ t := by
    have hngeom : n = ∑ i ∈ Finset.range (t + 1), q ^ i := by
      dsimp [n]
      rw [← Nat.geomSum_eq hq2 (t + 1)]
    have hdgeom : d = ∑ i ∈ Finset.range t, q ^ i := by
      dsimp [d]
      rw [← Nat.geomSum_eq hq2 t]
    rw [hngeom, hdgeom, Finset.sum_range_succ]
    omega
  have hAdjCard : Fintype.card {p : P × P // adj p.1 p.2} = n * d := by
    let e : {p : P × P // adj p.1 p.2} ≃
        Σ u : P, {v : P // adj u v} :=
      { toFun := fun p => ⟨p.1.1, ⟨p.1.2, p.2⟩⟩
        invFun := fun p => ⟨(p.1, p.2.1), p.2.2⟩
        left_inv := by intro p; rfl
        right_inv := by intro p; rfl }
    rw [Fintype.card_congr e, Fintype.card_sigma]
    simp only [hdegree]
    simp [hPn, nsmul_eq_mul, Nat.mul_comm]
  have hOldCard : Fintype.card {p : P × P // ¬ adj p.1 p.2} = n * q ^ t := by
    rw [Fintype.card_subtype_compl, Fintype.card_prod, hAdjCard]
    rw [hPn]
    rw [← hnsub]
    rw [Nat.mul_sub_left_distrib]
  have hpairbound : (q : ℝ) ^ (2 * t) / 2 ≤
      (Fintype.card {p : P × P // ¬ adj p.1 p.2} : ℝ) := by
    rw [hOldCard]
    have hnlowN : q ^ t ≤ n := by
      dsimp [n]
      rw [← Nat.geomSum_eq hq2 (t + 1)]
      rw [Finset.sum_range_succ]
      omega
    have hnlow : (q : ℝ) ^ t ≤ n := by
      exact_mod_cast hnlowN
    have hqtp : 0 ≤ (q : ℝ)^t := by positivity
    have hqpow2 : (q : ℝ) ^ (2*t) = (q:ℝ)^t * (q:ℝ)^t := by
      rw [← pow_add]
      congr 1 <;> omega
    rw [hqpow2]
    have hprod : (q : ℝ)^t * (q : ℝ)^t ≤ n * (q : ℝ)^t :=
      mul_le_mul_of_nonneg_right hnlow hqtp
    norm_num [Nat.cast_mul] at hprod ⊢
    nlinarith
  have hgeom_lower : ∀ r : Nat, q ^ r ≤ ∑ i ∈ Finset.range (r + 1), q ^ i := by
    intro r
    rw [Finset.sum_range_succ]
    omega
  have hgeom_upper : ∀ r : Nat, (∑ i ∈ Finset.range (r + 1), q ^ i) ≤ 2 * q ^ r := by
    intro r
    induction r with
    | zero => simp
    | succ r ihr =>
        rw [Finset.sum_range_succ, pow_succ]
        calc
          (∑ i ∈ Finset.range (r + 1), q ^ i) + q ^ r * q ≤
              2 * q ^ r + q ^ r * q := Nat.add_le_add_right ihr _
          _ ≤ q ^ r * q + q ^ r * q := by
              apply Nat.add_le_add_right
              simpa [Nat.mul_comm] using Nat.mul_le_mul_right (q ^ r) hq2
          _ = 2 * (q ^ r * q) := by ring
  have hnlowN : q ^ t ≤ n := by
    dsimp [n]
    rw [← Nat.geomSum_eq hq2 (t + 1)]
    exact hgeom_lower t
  have hnupN : n ≤ 2 * q ^ t := by
    dsimp [n]
    rw [← Nat.geomSum_eq hq2 (t + 1)]
    exact hgeom_upper t
  have hdlowN : q ^ (t - 1) ≤ d := by
    dsimp [d]
    rw [← Nat.geomSum_eq hq2 t]
    simpa [show t - 1 + 1 = t by omega] using hgeom_lower (t - 1)
  have hdupN : d ≤ 2 * q ^ (t - 1) := by
    dsimp [d]
    rw [← Nat.geomSum_eq hq2 t]
    simpa [show t - 1 + 1 = t by omega] using hgeom_upper (t - 1)
  have hnlow : (q : ℝ) ^ t / 2 ≤ n := by
    have h := hnlowN
    norm_num [Nat.cast_pow] at h ⊢
    exact_mod_cast (show (q ^ t : ℝ) / 2 ≤ (n : ℝ) by
      have h' : (q ^ t : ℝ) ≤ n := by exact_mod_cast h
      linarith)
  have hnup : (n : ℝ) ≤ 2 * (q : ℝ) ^ t := by
    exact_mod_cast hnupN
  have hdlow : (q : ℝ) ^ (t - 1) / 2 ≤ d := by
    have h' : (q ^ (t - 1) : ℝ) ≤ d := by exact_mod_cast hdlowN
    linarith
  have hdup : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
    exact_mod_cast hdupN
  exact ⟨hnlow, hnup, hdlow, hdup, hlam, by
    change (q : ℝ) ^ (2 * t) / 2 ≤
      (Fintype.card {p : P × P // ¬ adj p.1 p.2} : ℝ)
    exact hpairbound⟩
