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
open LinearMap (BilinForm)

set_option maxHeartbeats 8000000

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
  dsimp
  intro n d lambda hgraph hA hCA hC4 hCq hk
  rcases hgraph with ⟨hcard, hdeg, hmix, hnlow, hnhigh, hdlow, hdhigh, hlam⟩
  let G : LoopGraph := PolarityGraph K t ht
  letI : Fintype G.vertex := G.fintype
  letI : DecidableEq G.vertex := Classical.decEq _
  letI : DecidableRel G.adj := G.decidableAdj
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
  let V := Fin (t + 1) → K
  let B : BilinForm K V := dotProductBilin K K
  have hB : B.Nondegenerate := by
    constructor
    · intro x hx
      apply dotProduct_eq_zero_iff.mp
      intro y
      exact hx y
    · intro y hy
      apply dotProduct_eq_zero_iff.mp
      intro x
      change y ⬝ᵥ x = 0
      have hy' := hy x
      change x ⬝ᵥ y = 0 at hy'
      simpa [dotProduct_comm] using hy'
  have hadj (u v : G.vertex) : G.adj u v ↔ u.rep ⬝ᵥ v.rep = 0 := by
    change Projectivization.orthogonal u v ↔ _
    have hu : Projectivization.mk K u.rep u.rep_nonzero = u := u.mk_rep
    have hv : Projectivization.mk K v.rep v.rep_nonzero = v := v.mk_rep
    have hurep : (Projectivization.mk K u.rep u.rep_nonzero).rep = u.rep := by rw [hu]
    have hvrep : (Projectivization.mk K v.rep v.rep_nonzero).rep = v.rep := by rw [hv]
    rw [← hu, ← hv]
    change Projectivization.orthogonal
        (Projectivization.mk K u.rep u.rep_nonzero)
        (Projectivization.mk K v.rep v.rep_nonzero) ↔
      (Projectivization.mk K u.rep u.rep_nonzero).rep ⬝ᵥ
        (Projectivization.mk K v.rep v.rep_nonzero).rep = 0
    rw [hurep, hvrep]
    exact
      (Projectivization.orthogonal_mk (F := K) (m := Fin (t + 1))
        u.rep_nonzero v.rep_nonzero)
  let avec (x : D.vertex) : G.vertex := x.1.1
  let bvec (x : D.vertex) : G.vertex := x.1.2
  let avec' (x : D.vertex) : V := (avec x).rep
  let bvec' (x : D.vertex) : V := (bvec x).rep
  let S : ∀ m : Nat, (Fin m → D.vertex) → G.vertex → Finset V :=
    fun m f y => (Finset.univ.filter (fun i => G.adj (avec (f i)) y)).image
      (fun i => bvec' (f i))
  let W : ∀ m : Nat, (Fin m → D.vertex) → G.vertex → Submodule K V :=
    fun m f y => Submodule.span K (S m f y : Set V)
  let rnk : ∀ m : Nat, (Fin m → D.vertex) → G.vertex → Nat :=
    fun m f y => Module.finrank K (W m f y)
  let U : ∀ m : Nat, (Fin m → D.vertex) → Nat → Finset G.vertex :=
    fun m f r => Finset.univ.filter (fun y => rnk m f y ≤ r)
  let Z : ∀ m : Nat, (Fin m → D.vertex) → Nat → Finset G.vertex :=
    fun m f r => Finset.univ.filter (fun y => rnk m f y = r)
  let candidate : ∀ m : Nat, (Fin m → D.vertex) → Nat → Nat → Prop :=
    fun m f r l => l ≤ r ∧ (U m f r).card > 0 ∧
      ∀ j, j ≤ r → (Z m f j).card ≤ (Z m f l).card
  have proj_mem_card : ∀ (W0 : Submodule K V) (S0 : Finset G.vertex),
      (S0.filter (fun p : G.vertex => p.rep ∈ W0)).card ≤
        Nat.card (Projectivization K W0) := by
    intro W0 S0
    let T := S0.filter (fun p : G.vertex => p.rep ∈ W0)
    let f : T → Projectivization K W0 := fun p =>
      Projectivization.mk K ⟨p.1.rep, (Finset.mem_filter.mp p.2).2⟩ (by
        intro h
        exact p.1.rep_nonzero (Subtype.ext_iff.mp h))
    have hf : Function.Injective f := by
      intro p p' h
      apply Subtype.ext
      have hh := (Projectivization.mk_eq_mk_iff' K (V := W0) _ _ _ _).mp h
      rcases hh with ⟨c, hc⟩
      change (p.val : Projectivization K V) = (p'.val : Projectivization K V)
      have h1 : (p.val : Projectivization K V) =
          Projectivization.mk K (V := V) p.1.rep p.1.rep_nonzero := p.1.mk_rep.symm
      have h2 : Projectivization.mk K (V := V) p.1.rep p.1.rep_nonzero =
          Projectivization.mk K (V := V) p'.1.rep p'.1.rep_nonzero := by
        apply (Projectivization.mk_eq_mk_iff' K (V := V) _ _ p.1.rep_nonzero
          p'.1.rep_nonzero).mpr
        refine ⟨c, ?_⟩
        simpa using congrArg Subtype.val hc
      have h3 : Projectivization.mk K (V := V) p'.1.rep p'.1.rep_nonzero =
          (p'.val : Projectivization K V) := p'.1.mk_rep
      exact h1.trans (h2.trans h3)
    have hc := Nat.card_le_card_of_injective f hf
    have hleft : Nat.card T = Fintype.card T := Nat.card_eq_fintype_card
    rw [hleft, Fintype.card_coe] at hc
    exact hc
  have hK2 : 2 ≤ Fintype.card K := by
    have hlt : 1 < Fintype.card K := by
      simpa [hK] using (Finite.one_lt_card : 1 < Nat.card K)
    omega
  have hspan_bound : ∀ (m : Nat) (f : Fin m → D.vertex) (y : G.vertex),
      1 ≤ rnk m f y → Nat.card (Projectivization K (W m f y)) ≤
        2 * q ^ (rnk m f y - 1) := by
    intro m f y hr
    have hh := (ProjectiveSpanPointBound K V (S m f y)).2.2 hr
    simpa [rnk, hK] using hh
  have hspan_zero : ∀ (m : Nat) (f : Fin m → D.vertex) (y : G.vertex),
      rnk m f y = 0 → Nat.card (Projectivization K (W m f y)) = 0 := by
    intro m f y hr
    have hh := (ProjectiveSpanPointBound K V (S m f y)).2.1 hr
    simpa [rnk] using hh
  have horth_bound : ∀ (W0 : Submodule K V),
      Nat.card (Projectivization K (B.orthogonal W0)) ≤
        2 * q ^ (Module.finrank K (B.orthogonal W0) - 1) := by
    intro W0
    have hh := (OrthogonalComplementCardinality K V B hB W0 hK2).2
    simpa [hK] using hh
  have hcandidate : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      (U m f r).card > 0 → ∃ l, candidate m f r l := by
    intro m f r hU
    let T : Finset Nat := Finset.range (r + 1)
    have hT : T.Nonempty := by
      exact ⟨0, by simp [T]⟩
    let vals : Finset Nat := T.image (fun j => (Z m f j).card)
    have hvals : vals.Nonempty := by
      exact ⟨(Z m f 0).card, Finset.mem_image.mpr ⟨0, by simp [T], rfl⟩⟩
    let M := vals.max' hvals
    have hM : M ∈ vals := Finset.max'_mem vals hvals
    rcases Finset.mem_image.mp hM with ⟨l, hlT, hlM⟩
    refine ⟨l, ?_⟩
    refine ⟨by simpa [T] using hlT, hU, ?_⟩
    intro j hj
    have hjT : j ∈ T := by simpa [T] using hj
    have hjvals : (Z m f j).card ∈ vals := Finset.mem_image.mpr ⟨j, hjT, rfl⟩
    have hleM : (Z m f j).card ≤ M := Finset.le_max' vals _ hjvals
    simpa [hlM] using hleM
  let ell : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat), Nat :=
    fun m f r => if h : (U m f r).card > 0 then
      Classical.choose (hcandidate m f r h) else 0
  let popular : ∀ m : Nat, (Fin m → D.vertex) → Nat → G.vertex → Prop :=
    fun m f r b => rnk m f b = r ∧
      (Z m f (ell m f r)).card ≤ 16 * q *
        ((Z m f (ell m f r)).filter (fun y => b.rep ∈ W m f y)).card
  let poor : ∀ m : Nat, (Fin m → D.vertex) → Nat → G.vertex → Prop :=
    fun m f r a =>
      8 * q * ((Z m f (ell m f r)).filter (fun y => G.adj a y)).card ≤
        (Z m f (ell m f r)).card
  let marked : ∀ m : Nat, (Fin m → D.vertex) → Prop := fun m f =>
    match m with
    | 0 => True
    | m + 1 =>
      let p := Fin.init f
      let x := f (Fin.last m)
      popular m p (rnk m p (bvec x)) (bvec x) ∨
        poor m p (rnk m p (bvec x)) (avec x)
  have hell : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      (U m f r).card > 0 → candidate m f r (ell m f r) := by
    intro m f r hU
    dsimp [ell]
    split
    next h => exact Classical.choose_spec (hcandidate m f r h)
    next h => exact False.elim (h hU)
  have hell_mem_pos : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      (U m f r).card > 0 → (Z m f (ell m f r)).card > 0 := by
    intro m f r hU
    have he := hell m f r hU
    rcases Finset.card_pos.mp hU with ⟨y, hy⟩
    have hyr : rnk m f y ≤ r := (Finset.mem_filter.mp hy).2
    let j := rnk m f y
    have hj : j ≤ r := hyr
    have hyz : y ∈ Z m f j := by
      exact Finset.mem_filter.mpr ⟨by simp, by rfl⟩
    have hle := he.2.2 j hj
    by_contra hz
    have hz0 : (Z m f (ell m f r)).card = 0 := Nat.eq_zero_of_not_pos hz
    have hzj : (Z m f j).card = 0 := by omega
    exact Nat.ne_of_gt (Finset.card_pos.mpr ⟨y, hyz⟩) hzj
  let valid : ∀ m : Nat, (Fin m → D.vertex) → Prop := fun m f =>
    ∀ ⦃i j : Fin m⦄, i.val < j.val → ¬ D.arc (f i) (f j)
  have valid_tuple : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
      valid m σ.vertex := by
    intro m σ
    exact σ.independent
  have h_ext_orth : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex),
      valid (m + 1) (Fin.snoc f x) →
      (avec' x) ∈ B.orthogonal (W m f (bvec x)) := by
    intro m f x hx
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro v hv
    induction hv using Submodule.span_induction with
    | mem v hv =>
        rcases Finset.mem_image.mp (show v ∈ S m f (bvec x) from hv) with ⟨i, hi, hvi⟩
        rw [← hvi]
        have hi' : G.adj (avec (f i)) (bvec x) :=
          (Finset.mem_filter.mp hi).2
        have hno := hx (i := i.castSucc) (j := Fin.last m) i.isLt
        have hback : G.adj (avec x) (bvec (f i)) := by
          by_contra hnot
          apply (show ¬ (G.adj (avec (f i)) (bvec x) ∧
              ¬ G.adj (avec x) (bvec (f i))) by
            simpa [D, avec, bvec, Fin.snoc_castSucc, Fin.snoc_last] using hno)
          exact ⟨hi', hnot⟩
        have hdot := (hadj (avec x) (bvec (f i))).mp hback
        change B (bvec' (f i)) (avec' x) = 0
        change (bvec' (f i)) ⬝ᵥ (avec' x) = 0
        simpa [dotProduct_comm] using hdot
    | zero => simp [B]
    | add v w hv hw ihv ihw =>
        change B (v + w) (avec' x) = 0
        rw [LinearMap.BilinForm.add_left, ihv, ihw, add_zero]
    | smul c v hv ih =>
        change B (c • v) (avec' x) = 0
        rw [LinearMap.BilinForm.smul_left, ih, mul_zero]
  have h_ext_card : ∀ (m : Nat) (f : Fin m → D.vertex) (b : G.vertex)
      (r : Nat), r ≤ t → (U m f r).card > 0 → rnk m f b = r →
      Fintype.card {x : D.vertex // bvec x = b ∧
        valid (m + 1) (Fin.snoc f x)} ≤ 2 * q ^ (t - r) := by
    intro m f b r hr hU hrank
    let E : Type := {x : D.vertex // bvec x = b ∧
      valid (m + 1) (Fin.snoc f x)}
    let T : Type := {a : G.vertex // a.rep ∈ B.orthogonal (W m f b)}
    let e : E → T := fun x => ⟨avec x.1, by
      have hx := h_ext_orth m f x.1 x.2.2
      simpa [x.2.1] using hx⟩
    have he : Function.Injective e := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · simpa [avec] using congrArg Subtype.val hxy
      · exact (x.2.1.trans y.2.1.symm)
    have hle : Fintype.card E ≤ Fintype.card T :=
      Fintype.card_le_of_injective e he
    have hproj : (Finset.univ.filter
        (fun a : G.vertex => a.rep ∈ B.orthogonal (W m f b))).card ≤
        Nat.card (Projectivization K (B.orthogonal (W m f b))) := by
      simpa using proj_mem_card (B.orthogonal (W m f b)) (Finset.univ : Finset G.vertex)
    have hTE : Fintype.card T =
        (Finset.univ.filter
          (fun a : G.vertex => a.rep ∈ B.orthogonal (W m f b))).card := by
      exact Fintype.card_subtype _
    have hcard : Fintype.card E ≤
        Nat.card (Projectivization K (B.orthogonal (W m f b))) :=
      hle.trans (hTE ▸ hproj)
    have hdim := (OrthogonalComplementCardinality K V B hB
      (W m f b) hK2).1
    have hdim' : Module.finrank K (B.orthogonal (W m f b)) = t + 1 - r := by
      have hWr : Module.finrank K (W m f b) = r := by
        simpa [rnk] using hrank
      rw [hdim, hWr]
      simp [V]
    have hbound := horth_bound (W m f b)
    rw [hdim'] at hbound
    have hpow : t + 1 - r - 1 = t - r := by omega
    rw [hpow] at hbound
    exact hcard.trans hbound
  have incidence_right : ∀ {X Y : Type} [Fintype X] [Fintype Y]
      (P : Finset X) (Z0 : Finset Y) (R : X → Y → Prop) [DecidableRel R],
      ((P.product Z0).filter (fun e => R e.1 e.2)).card =
        Finset.sum Z0 (fun y => (P.filter (fun x => R x y)).card) := by
    intro X Y _ _ P Z0 R _
    calc
      ((P.product Z0).filter (fun e => R e.1 e.2)).card =
          ∑ e ∈ P.product Z0, if R e.1 e.2 then (1 : Nat) else 0 := by
        exact (Finset.sum_boole (R := Nat) (fun e => R e.1 e.2)
          (P.product Z0)).symm
      _ = ∑ y ∈ Z0, ∑ x ∈ P, if R x y then (1 : Nat) else 0 := by
        exact Finset.sum_product_right P Z0 (fun e => if R e.1 e.2 then (1 : Nat) else 0)
      _ = Finset.sum Z0 (fun y => (P.filter (fun x => R x y)).card) := by
        apply Finset.sum_congr rfl
        intro y hy
        exact Finset.sum_boole (R := Nat) (fun x => R x y) P
  have incidence_left : ∀ {X Y : Type} [Fintype X] [Fintype Y]
      (P : Finset X) (Z0 : Finset Y) (R : X → Y → Prop) [DecidableRel R],
      ((P.product Z0).filter (fun e => R e.1 e.2)).card =
        Finset.sum P (fun x => (Z0.filter (fun y => R x y)).card) := by
    intro X Y _ _ P Z0 R _
    calc
      ((P.product Z0).filter (fun e => R e.1 e.2)).card =
          ∑ e ∈ P.product Z0, if R e.1 e.2 then (1 : Nat) else 0 := by
        exact (Finset.sum_boole (R := Nat) (fun e => R e.1 e.2)
          (P.product Z0)).symm
      _ = ∑ x ∈ P, ∑ y ∈ Z0, if R x y then (1 : Nat) else 0 := by
        exact Finset.sum_product' P Z0
          (fun x y => if R x y then (1 : Nat) else 0)
      _ = Finset.sum P (fun x => (Z0.filter (fun y => R x y)).card) := by
        apply Finset.sum_congr rfl
        intro x hx
        exact Finset.sum_boole (R := Nat) (fun y => R x y) Z0
  have h_ext_none : ∀ (m : Nat) (f : Fin m → D.vertex)
      (x : D.vertex), valid (m + 1) (Fin.snoc f x) →
      rnk m f (bvec x) = t + 1 → False := by
    intro m f x hx hrank
    have hdim := (OrthogonalComplementCardinality K V B hB
      (W m f (bvec x)) hK2).1
    have hdim0 : Module.finrank K (B.orthogonal (W m f (bvec x))) = 0 := by
      have hWr : Module.finrank K (W m f (bvec x)) = t + 1 := by
        simpa [rnk] using hrank
      rw [hdim, hWr]
      simp [V]
    have hsub : Subsingleton (B.orthogonal (W m f (bvec x)) : Type) :=
      Module.finrank_zero_iff.mp hdim0
    have hxorth := h_ext_orth m f x hx
    let z : B.orthogonal (W m f (bvec x)) := ⟨avec' x, hxorth⟩
    have hz : z = 0 := Subsingleton.elim _ _
    have hz' : avec' x = 0 := congrArg Subtype.val hz
    exact (avec x).rep_nonzero hz'
  have h_rank_le : ∀ (m : Nat) (f : Fin m → D.vertex) (y : G.vertex),
      rnk m f y ≤ t + 1 := by
    intro m f y
    have hh := Submodule.finrank_le (W m f y)
    simpa [rnk, V] using hh
  have h_rank_lt_ext : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex),
      valid (m + 1) (Fin.snoc f x) → rnk m f (bvec x) < t + 1 := by
    intro m f x hx
    have hle := h_rank_le m f (bvec x)
    by_contra hnot
    have heq : rnk m f (bvec x) = t + 1 := by omega
    exact h_ext_none m f x hx heq
  have hpop_card : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      r ≤ t → (U m f r).card > 0 →
      let l := ell m f r
      (Finset.univ.filter (fun b : G.vertex =>
        rnk m f b = r ∧
          (Z m f l).card ≤ 16 * q *
            ((Z m f l).filter (fun y => b.rep ∈ W m f y)).card)).card ≤
        32 * q ^ r := by
    intro m f r hr hU
    let l := ell m f r
    let P := Finset.univ.filter (fun b : G.vertex =>
      rnk m f b = r ∧
        (Z m f l).card ≤ 16 * q *
          ((Z m f l).filter (fun y => b.rep ∈ W m f y)).card)
    let Zl := Z m f l
    have hZpos : Zl.card > 0 := by
      simpa [Zl, l] using hell_mem_pos m f r hU
    let I := (P.product Zl).filter
      (fun e => e.1.rep ∈ W m f e.2)
    have hI_left : I.card = Finset.sum P
        (fun b => (Zl.filter (fun y => b.rep ∈ W m f y)).card) := by
      exact incidence_left P Zl (fun b y => b.rep ∈ W m f y)
    have hI_right : I.card = Finset.sum Zl
        (fun y => (P.filter (fun b => b.rep ∈ W m f y)).card) := by
      exact incidence_right P Zl (fun b y => b.rep ∈ W m f y)
    have hinc_single : ∀ y ∈ Zl,
        (P.filter (fun b => b.rep ∈ W m f y)).card ≤
          2 * q ^ (l - 1) := by
      intro y hy
      have hyr : rnk m f y = l := (Finset.mem_filter.mp hy).2
      by_cases hl0 : l = 0
      · have hz := hspan_zero m f y (by simpa [hl0] using hyr)
        have hle := proj_mem_card (W m f y) P
        have hzero : (P.filter (fun b => b.rep ∈ W m f y)).card = 0 := by
          apply le_antisymm
          · exact hle.trans_eq hz
          · omega
        rw [hzero]
        simp
      · have hlpos : 1 ≤ l := by omega
        have hle := proj_mem_card (W m f y) P
        have hbound := hspan_bound m f y (by omega)
        rw [hyr] at hbound
        exact hle.trans hbound
    have hI_upper : I.card ≤ Zl.card * (2 * q ^ (l - 1)) := by
      rw [hI_right]
      calc
        Finset.sum Zl (fun y => (P.filter (fun b => b.rep ∈ W m f y)).card) ≤
            Finset.sum Zl (fun _ => 2 * q ^ (l - 1)) :=
          Finset.sum_le_sum (fun y hy => hinc_single y hy)
        _ = Zl.card * (2 * q ^ (l - 1)) := by simp [nsmul_eq_mul]
    have hI_lower : P.card * Zl.card ≤ 16 * q * I.card := by
      calc
        P.card * Zl.card = Finset.sum P (fun _ => Zl.card) := by
          simp [nsmul_eq_mul]
        _ ≤ Finset.sum P (fun b =>
            16 * q * (Zl.filter (fun y => b.rep ∈ W m f y)).card) := by
          apply Finset.sum_le_sum
          intro b hb
          exact (Finset.mem_filter.mp hb).2.2
        _ = 16 * q * I.card := by
          calc
            Finset.sum P (fun b =>
                16 * q * (Zl.filter (fun y => b.rep ∈ W m f y)).card) =
                16 * q * (Finset.sum P (fun b =>
                  (Zl.filter (fun y => b.rep ∈ W m f y)).card)) := by
              rw [Finset.mul_sum]
            _ = 16 * q * I.card := by
              exact congrArg (fun z => 16 * q * z) hI_left.symm
    have hPbound : P.card ≤ 32 * q ^ l := by
      by_cases hl0 : l = 0
      · have hIzero : I.card = 0 := by
          rw [hI_right]
          apply Finset.sum_eq_zero
          intro y hy
          have hyr : rnk m f y = l := (Finset.mem_filter.mp hy).2
          have hz := hspan_zero m f y (by simpa [hl0] using hyr)
          have hle := proj_mem_card (W m f y) P
          have hzero : (P.filter (fun b => b.rep ∈ W m f y)).card = 0 := by
            apply le_antisymm
            · exact hle.trans_eq hz
            · omega
          exact hzero
        have hmul : P.card * Zl.card ≤ 0 :=
          hI_lower.trans (by simp [hIzero])
        have hPzero : P.card = 0 := by
          by_contra hp
          have hp' : 0 < P.card := Nat.pos_of_ne_zero hp
          have hprod : 0 < P.card * Zl.card := Nat.mul_pos hp' hZpos
          omega
        simp [hPzero]
      · have hlpos : 1 ≤ l := by omega
        have hmul : P.card * Zl.card ≤ (32 * q ^ l) * Zl.card := by
          calc
            P.card * Zl.card ≤ 16 * q * I.card := hI_lower
            _ ≤ 16 * q * (Zl.card * (2 * q ^ (l - 1))) := by
              gcongr
            _ = (32 * q ^ l) * Zl.card := by
              have hpow' : q ^ l = q ^ (l - 1) * q := by
                conv_lhs => rw [show l = (l - 1) + 1 by omega]
                rw [pow_add, pow_one]
              rw [hpow']
              ring
        exact Nat.le_of_mul_le_mul_right hmul hZpos
    have hpow : q ^ l ≤ q ^ r := Nat.pow_le_pow_right (by omega) (hell m f r hU).1
    dsimp [P]
    exact hPbound.trans (Nat.mul_le_mul_left 32 hpow)
  have hGcard : Fintype.card G.vertex = n := by
    simpa [G] using hcard
  have hmix_fin : ∀ X Y : Finset G.vertex,
      |((X.product Y).filter (fun e => G.adj e.1 e.2)).card -
          (d : ℝ) / n * X.card * Y.card| ≤
        lambda * Real.sqrt (X.card * Y.card) := by
    intro X Y
    exact ExpanderMixing G.adj n d lambda hGcard (by
      intro x y
      simpa [G] using hmix x y) X Y
  have hn : 0 < n := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hp : (0 : ℝ) < (q : ℝ) ^ t / 2 := by positivity
    have : (0 : ℝ) < n := lt_of_lt_of_le hp hnlow
    exact_mod_cast this
  have hd : 0 < d := by
    have hqpos : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hp : (0 : ℝ) < (q : ℝ) ^ (t - 1) / 2 := by positivity
    have : (0 : ℝ) < d := lt_of_lt_of_le hp hdlow
    exact_mod_cast this
  have hqR : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hratio_lower : 1 / (4 * (q : ℝ)) ≤ (d : ℝ) / n := by
    have hqpow : (q : ℝ) ^ (t - 1) ≤ 2 * d := by nlinarith [hdlow]
    have hstep : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * q := by
      conv_lhs => rw [show t = (t - 1) + 1 by omega]
      rw [pow_add, pow_one]
    have hqt : (q : ℝ) ^ t ≤ 2 * q * d := by
      rw [hstep]
      nlinarith [hqpow]
    have hn' : (n : ℝ) ≤ 4 * q * d := by
      calc
        (n : ℝ) ≤ 2 * (q : ℝ) ^ t := hnhigh
        _ ≤ 2 * (2 * q * d) := by gcongr
        _ = 4 * q * d := by ring
    apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * q)
      (by positivity : (0 : ℝ) < n)).2
    nlinarith [hn']
  have hratio_upper : (d : ℝ) / n ≤ 4 / (q : ℝ) := by
    have hnlow' : (q : ℝ) ^ t / 2 ≤ n := hnlow
    have hqd : (q : ℝ) * d ≤ 2 * (q : ℝ) ^ t := by
      have hstep : (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * q := by
        conv_lhs => rw [show t = (t - 1) + 1 by omega]
        rw [pow_add, pow_one]
      rw [hstep]
      nlinarith [hdhigh]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < n)).2
    calc
      (d : ℝ) ≤ (4 * n) / q := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < q)).2
        nlinarith [hqd, hnlow']
      _ = 4 / q * n := by ring
  have hpoor_card : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      r ≤ t → (U m f r).card > 0 →
      let l := ell m f r
      Fintype.card {x : D.vertex //
        valid (m + 1) (Fin.snoc f x) ∧
        rnk m f (bvec x) = r ∧ poor m f r (avec x)} ≤ 5000 * q ^ t := by
    intro m f r hr hU
    let l := ell m f r
    let P := Finset.univ.filter (fun a : G.vertex =>
      8 * q * ((Z m f l).filter (fun y => G.adj a y)).card ≤
        (Z m f l).card)
    let Zl := Z m f l
    have hZpos : Zl.card > 0 := by
      simpa [Zl, l] using hell_mem_pos m f r hU
    have hnqd : (n : ℝ) ≤ 4 * (q : ℝ) * d := by
      have hh := (le_div_iff₀ (show (0 : ℝ) < n by exact_mod_cast hn)).mp
        hratio_lower
      field_simp [ne_of_gt (show (0 : ℝ) < q by exact_mod_cast (show 0 < q by omega))] at hh
      nlinarith [hh]
    have hA : ∀ a ∈ P,
        ((Zl.filter (fun y => G.adj a y)).card : ℝ) ≤
          (d : ℝ) * Zl.card / (2 * n) := by
      intro a ha
      have ha' := (Finset.mem_filter.mp ha).2
      have hpoor : 8 * q *
          ((Zl.filter (fun y => G.adj a y)).card : ℕ) ≤ Zl.card := ha'
      have hpoor' : 8 * (q : ℝ) *
          ((Zl.filter (fun y => G.adj a y)).card : ℝ) ≤ (Zl.card : ℝ) := by
        exact_mod_cast hpoor
      have hleft : ((Zl.filter (fun y => G.adj a y)).card : ℝ) ≤
          (Zl.card : ℝ) / (8 * q) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * q)).2
        nlinarith [hpoor']
      have hmul := mul_le_mul_of_nonneg_right hnqd
        (show (0 : ℝ) ≤ (Zl.card : ℝ) by positivity)
      have hright : (Zl.card : ℝ) / (8 * q) ≤
          (d : ℝ) * Zl.card / (2 * n) := by
        apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * q)
          (by positivity : (0 : ℝ) < 2 * n)).2
        nlinarith [hmul]
      exact hleft.trans hright
    have halon := AlonRodlBound G.adj n d lambda hGcard hmix_fin hn hd P Zl hA
    have hqtm1 : (q : ℝ) ^ (t - 1) ≤ 2 * d := by
      nlinarith [hdlow]
    have hn2 : (n : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ (2 * t) := by
      have hnnonneg : (0 : ℝ) ≤ n := by exact_mod_cast (show 0 ≤ n by omega)
      have hqtnonneg : (0 : ℝ) ≤ (q : ℝ) ^ t := by positivity
      have hsquare := mul_self_le_mul_self hnnonneg hnhigh
      calc
        (n : ℝ) ^ 2 = (n : ℝ) * n := by ring
        _ ≤ (2 * (q : ℝ) ^ t) * (2 * (q : ℝ) ^ t) := hsquare
        _ = 4 * (q : ℝ) ^ (2 * t) := by
          rw [show 2 * t = t + t by omega, pow_add]
          ring
    have hqrel : (q : ℝ) ^ (2 * t) ≤
        2 * (q : ℝ) ^ (t + 1) * d := by
      have hexp : 2 * t = (t + 1) + (t - 1) := by omega
      rw [hexp, pow_add]
      have hmul := mul_le_mul_of_nonneg_left hqtm1
        (show (0 : ℝ) ≤ (q : ℝ) ^ (t + 1) by positivity)
      nlinarith [hmul]
    have hn2' : (n : ℝ) ^ 2 ≤
        8 * (q : ℝ) ^ (t + 1) * d := by
      calc
        (n : ℝ) ^ 2 ≤ 4 * (q : ℝ) ^ (2 * t) := hn2
        _ ≤ 4 * (2 * (q : ℝ) ^ (t + 1) * d) := by gcongr
        _ = 8 * (q : ℝ) ^ (t + 1) * d := by ring
    have hprod_real : (P.card : ℝ) * Zl.card ≤
        1024 * (q : ℝ) ^ (t + 1) := by
      by_cases hzero : (P.card : ℝ) * Zl.card = 0
      · simp [hzero]
      · have hprodpos : 0 < (P.card : ℝ) * Zl.card := by
          exact lt_of_le_of_ne (by positivity) (Ne.symm hzero)
        have hedge : (((P.product Zl).filter (fun e => G.adj e.1 e.2)).card : ℝ) ≤
            (d : ℝ) / (2 * n) * P.card * Zl.card := by
          have hcount := incidence_left P Zl (fun a y => G.adj a y)
          calc
            (((P.product Zl).filter (fun e => G.adj e.1 e.2)).card : ℝ) =
                ∑ a ∈ P, ((Zl.filter (fun y => G.adj a y)).card : ℝ) := by
              exact_mod_cast hcount
            _ ≤ ∑ _a ∈ P, (d : ℝ) * Zl.card / (2 * n) := by
              exact Finset.sum_le_sum (fun a ha => hA a ha)
            _ = (d : ℝ) / (2 * n) * P.card * Zl.card := by
              simp
              ring
        have hhalf : (d : ℝ) / (2 * n) * P.card * Zl.card ≤
            |(((P.product Zl).filter (fun e => G.adj e.1 e.2)).card : ℝ) -
              (d : ℝ) / n * P.card * Zl.card| := by
          have habs := le_abs_self
            ((d : ℝ) / n * P.card * Zl.card -
              (((P.product Zl).filter (fun e => G.adj e.1 e.2)).card : ℝ))
          rw [abs_sub_comm] at habs
          have hrel : (d : ℝ) / (2 * n) * P.card * Zl.card =
              ((d : ℝ) / n * P.card * Zl.card) / 2 := by ring
          rw [hrel] at hedge ⊢
          linarith
        have hlammain := hhalf.trans (hmix_fin P Zl)
        have hsqrtpos : 0 < Real.sqrt ((P.card : ℝ) * Zl.card) :=
          Real.sqrt_pos.2 hprodpos
        have hleftpos : 0 < (d : ℝ) / (2 * n) * P.card * Zl.card := by
          have hbase : 0 < (d : ℝ) / (2 * n) := by positivity
          simpa [mul_assoc] using mul_pos hbase hprodpos
        have hlampos : 0 < lambda := by
          by_contra hnot
          have hnon : lambda ≤ 0 := le_of_not_gt hnot
          have hrhs : lambda * Real.sqrt ((P.card : ℝ) * Zl.card) ≤ 0 :=
            mul_nonpos_of_nonpos_of_nonneg hnon (le_of_lt hsqrtpos)
          linarith
        have hlam_sq : lambda ^ 2 ≤ 4 * (d : ℝ) := by
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
          nlinarith [hlam]
        have hmulden : 4 * lambda ^ 2 * (n : ℝ) ^ 2 ≤
            1024 * (q : ℝ) ^ (t + 1) * (d : ℝ) ^ 2 := by
          have hlamn := mul_le_mul_of_nonneg_right hlam_sq
            (show (0 : ℝ) ≤ (n : ℝ) ^ 2 by positivity)
          have h1 : 4 * lambda ^ 2 * (n : ℝ) ^ 2 ≤
              16 * (d : ℝ) * (n : ℝ) ^ 2 := by nlinarith [hlamn]
          have h2 := mul_le_mul_of_nonneg_left hn2'
            (show (0 : ℝ) ≤ 16 * (d : ℝ) by positivity)
          calc
            4 * lambda ^ 2 * (n : ℝ) ^ 2 ≤
                16 * (d : ℝ) * (n : ℝ) ^ 2 := h1
            _ ≤ 128 * (q : ℝ) ^ (t + 1) * (d : ℝ) ^ 2 := by nlinarith [h2]
            _ ≤ 1024 * (q : ℝ) ^ (t + 1) * (d : ℝ) ^ 2 := by
              nlinarith [show (0 : ℝ) ≤ (q : ℝ) ^ (t + 1) * (d : ℝ) ^ 2 by positivity]
        have hmain : 4 * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 ≤
            1024 * (q : ℝ) ^ (t + 1) := by
          calc
            4 * lambda ^ 2 / (d : ℝ) ^ 2 * (n : ℝ) ^ 2 =
                (4 * lambda ^ 2 * (n : ℝ) ^ 2) / (d : ℝ) ^ 2 := by ring
            _ ≤ (1024 * (q : ℝ) ^ (t + 1) * (d : ℝ) ^ 2) /
                (d : ℝ) ^ 2 := by
              exact (div_le_div_iff_of_pos_right
                (sq_pos_of_pos (show (0 : ℝ) < d by exact_mod_cast hd))).2 hmulden
            _ = 1024 * (q : ℝ) ^ (t + 1) := by
              field_simp
        exact halon.trans hmain
    have hprod : P.card * Zl.card ≤ 1024 * q ^ (t + 1) := by
      have hprod' : ((P.card * Zl.card : ℕ) : ℝ) ≤
          ((1024 * q ^ (t + 1) : ℕ) : ℝ) := by
        simpa [Nat.cast_mul, Nat.cast_pow] using hprod_real
      exact_mod_cast hprod'
    let Zr := Z m f r
    have hZr : Zr.card ≤ Zl.card := by
      have he := hell m f r hU
      exact he.2.2 r (le_refl r)
    have hprodZr : (P.card : ℝ) * Zr.card ≤
        1024 * (q : ℝ) ^ (t + 1) := by
      calc
        (P.card : ℝ) * Zr.card ≤ (P.card : ℝ) * Zl.card := by
          gcongr
        _ ≤ 1024 * (q : ℝ) ^ (t + 1) := hprod_real
    have hdecay : lambda * Real.sqrt ((P.card : ℝ) * Zr.card) ≤
        128 * (q : ℝ) ^ t := by
      by_cases hlamnonpos : lambda ≤ 0
      · have hsqrt : 0 ≤ Real.sqrt ((P.card : ℝ) * Zr.card) := Real.sqrt_nonneg _
        have hqtpos : 0 < (q : ℝ) ^ t := by positivity
        nlinarith
      · have hlampos : 0 < lambda := lt_of_not_ge hlamnonpos
        have hlam_sq : lambda ^ 2 ≤ 4 * (d : ℝ) := by
          have hs := Real.sq_sqrt (show (0 : ℝ) ≤ d by positivity)
          nlinarith [hlam]
        have hlamsmall : lambda ^ 2 ≤ 8 * (q : ℝ) ^ (t - 1) := by
          nlinarith [hlam_sq, hdhigh]
        have hmul := mul_le_mul hlamsmall hprodZr
          (show 0 ≤ (P.card : ℝ) * Zr.card by positivity)
          (show 0 ≤ 8 * (q : ℝ) ^ (t - 1) by positivity)
        have hsqrt := Real.sq_sqrt
          (show 0 ≤ (P.card : ℝ) * Zr.card by positivity)
        have hexp : (t - 1) + (t + 1) = 2 * t := by omega
        have hsq : (lambda * Real.sqrt ((P.card : ℝ) * Zr.card)) ^ 2 ≤
            (128 * (q : ℝ) ^ t) ^ 2 := by
          calc
            (lambda * Real.sqrt ((P.card : ℝ) * Zr.card)) ^ 2 =
                lambda ^ 2 * ((P.card : ℝ) * Zr.card) := by
              rw [mul_pow, hsqrt]
            _ ≤ (8 * (q : ℝ) ^ (t - 1)) *
                (1024 * (q : ℝ) ^ (t + 1)) := hmul
            _ = 8192 * (q : ℝ) ^ (2 * t) := by
              have hpowprod : (q : ℝ) ^ (t - 1) * (q : ℝ) ^ (t + 1) =
                  (q : ℝ) ^ (2 * t) := by
                calc
                  (q : ℝ) ^ (t - 1) * (q : ℝ) ^ (t + 1) =
                      (q : ℝ) ^ ((t - 1) + (t + 1)) :=
                    (pow_add (q : ℝ) (t - 1) (t + 1)).symm
                  _ = (q : ℝ) ^ (2 * t) := by congr 1 <;> omega
              calc
                (8 * (q : ℝ) ^ (t - 1)) *
                    (1024 * (q : ℝ) ^ (t + 1)) =
                    8192 * ((q : ℝ) ^ (t - 1) * (q : ℝ) ^ (t + 1)) := by ring
                _ = 8192 * (q : ℝ) ^ (2 * t) := by rw [hpowprod]
            _ ≤ (128 * (q : ℝ) ^ t) ^ 2 := by
              have hpowtwo : (q : ℝ) ^ (2 * t) =
                  (q : ℝ) ^ t * (q : ℝ) ^ t := by
                rw [show 2 * t = t + t by omega, pow_add]
              rw [pow_two, hpowtwo]
              nlinarith [show (0 : ℝ) ≤ (q : ℝ) ^ t by positivity]
        have hleft : 0 ≤ lambda * Real.sqrt ((P.card : ℝ) * Zr.card) := by positivity
        have hright : 0 ≤ 128 * (q : ℝ) ^ t := by positivity
        nlinarith [hsq]
    have hinc := IncidenceDecayBound G.adj q t n d lambda hq ht hn hd
      hmix_fin hratio_upper P Zl Zr hprod_real hZr hdecay
    let X : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧
      rnk m f (bvec x) = r ∧ poor m f r (avec x)}
    let E : Type := (P.product Zr).filter (fun e => G.adj e.1 e.2)
    let e : X → E := fun x => ⟨(avec x.1, bvec x.1), by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr ?_, ?_⟩
      · exact ⟨by simpa [P, poor, l] using x.2.2.2, by
          exact Finset.mem_filter.mpr ⟨by simp, x.2.2.1⟩⟩
      · simpa [D, avec, bvec] using x.1.property⟩
    have he : Function.Injective e := by
      intro x y hxy
      dsimp [e] at hxy
      apply Subtype.ext
      apply Subtype.ext
      have hpair : (avec x.1, bvec x.1) = (avec y.1, bvec y.1) :=
        congrArg (fun z : E => z.1) hxy
      simpa [avec, bvec] using hpair
    have hle : Fintype.card X ≤ Fintype.card E :=
      Fintype.card_le_of_injective e he
    have hEcard : Fintype.card E =
        ((P.product Zr).filter (fun e => G.adj e.1 e.2)).card :=
      by simpa only [E] using
        (Fintype.card_coe ((P.product Zr).filter (fun e => G.adj e.1 e.2)))
    have hNat : Fintype.card X ≤ 5000 * q ^ t := by
      calc
        Fintype.card X ≤ Fintype.card E := hle
        _ = (((P.product Zr).filter (fun e => G.adj e.1 e.2)).card : ℕ) := hEcard
        _ ≤ 5000 * q ^ t := by
          exact_mod_cast hinc
    dsimp [P, Zl, Zr, l, X]
    exact hNat
  have hpopular_child : ∀ (m : Nat) (f : Fin m → D.vertex) (r : Nat),
      r ≤ t → (U m f r).card > 0 →
      let l := ell m f r
      let P := Finset.univ.filter (fun b : G.vertex => popular m f r b)
      Fintype.card {x : D.vertex //
        valid (m + 1) (Fin.snoc f x) ∧
        rnk m f (bvec x) = r ∧ popular m f r (bvec x)} ≤ 64 * q ^ t := by
    intro m f r hr hU
    let l := ell m f r
    let P := Finset.univ.filter (fun b : G.vertex => popular m f r b)
    let Fib : P → Type := fun b =>
      {x : D.vertex // bvec x = b.1 ∧ valid (m + 1) (Fin.snoc f x)}
    let E : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧
      rnk m f (bvec x) = r ∧ popular m f r (bvec x)}
    let e : E → Sigma Fib := fun x =>
      ⟨⟨bvec x.1, Finset.mem_filter.mpr ⟨by simp [P], x.2.2.2⟩⟩,
        ⟨x.1, rfl, x.2.1⟩⟩
    have he : Function.Injective e := by
      intro x y hxy
      dsimp [e] at hxy
      have hv : (x.1 : D.vertex) = y.1 := by
        simpa using congrArg (fun z : Sigma Fib => z.2.1) hxy
      exact Subtype.ext hv
    have hE : Fintype.card E ≤ Fintype.card (Sigma Fib) :=
      Fintype.card_le_of_injective e he
    have hPcard : P.card ≤ 32 * q ^ r := by
      simpa [P, popular] using hpop_card m f r hr hU
    have hFib : ∀ b : P, Fintype.card (Fib b) ≤ 2 * q ^ (t - r) := by
      intro b
      have hb := (Finset.mem_filter.mp b.2).2
      have hbr : rnk m f b.1 = r := hb.1
      simpa [Fib] using h_ext_card m f b.1 r hr hU hbr
    have hsum : Fintype.card (Sigma Fib) ≤
        Fintype.card P * (2 * q ^ (t - r)) := by
      rw [Fintype.card_sigma]
      calc
        (∑ b, Fintype.card (Fib b)) ≤
            ∑ _b : P, 2 * q ^ (t - r) :=
          Finset.sum_le_sum (fun b _ => hFib b)
        _ = Fintype.card P * (2 * q ^ (t - r)) := by simp
    have hbound : Fintype.card E ≤
        (32 * q ^ r) * (2 * q ^ (t - r)) := by
      calc
        Fintype.card E ≤ Fintype.card (Sigma Fib) := hE
        _ ≤ Fintype.card P * (2 * q ^ (t - r)) := hsum
        _ ≤ (32 * q ^ r) * (2 * q ^ (t - r)) := by
          gcongr
          simpa using hPcard
    have hpow : q ^ r * q ^ (t - r) = q ^ t := by
      rw [← pow_add, Nat.add_sub_of_le hr]
    calc
      Fintype.card E ≤ (32 * q ^ r) * (2 * q ^ (t - r)) := hbound
      _ = 64 * q ^ t := by rw [show (32 : Nat) * q ^ r * (2 * q ^ (t - r)) =
          64 * (q ^ r * q ^ (t - r)) by ring, hpow]
  have hmarked_raw : ∀ (m : Nat) (f : Fin m → D.vertex),
      Fintype.card {x : D.vertex //
        valid (m + 1) (Fin.snoc f x) ∧
        marked (m + 1) (Fin.snoc f x)} ≤ A * q ^ t := by
    intro m f
    let Rpop : Fin (t + 1) → Type := fun r =>
      {x : D.vertex // valid (m + 1) (Fin.snoc f x) ∧
        rnk m f (bvec x) = (r : Nat) ∧ popular m f (r : Nat) (bvec x)}
    let Epop : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧
      popular m f (rnk m f (bvec x)) (bvec x)}
    let epop : Epop → Sigma Rpop := fun x =>
      let r : Fin (t + 1) := ⟨rnk m f (bvec x.1),
        h_rank_lt_ext m f x.1 x.2.1⟩
      ⟨r, ⟨x.1, x.2.1, rfl, x.2.2⟩⟩
    have hepop : Function.Injective epop := by
      intro x y hxy
      dsimp [epop] at hxy
      have hv : (x.1 : D.vertex) = y.1 := by
        simpa using congrArg (fun z : Sigma Rpop => z.2.1) hxy
      exact Subtype.ext hv
    have hpop_sum : Fintype.card Epop ≤
        64 * (t + 1) * q ^ t := by
      have hi : Fintype.card Epop ≤ Fintype.card (Sigma Rpop) :=
        Fintype.card_le_of_injective epop hepop
      have hs : Fintype.card (Sigma Rpop) ≤
          (t + 1) * (64 * q ^ t) := by
        rw [Fintype.card_sigma]
        calc
          (∑ r, Fintype.card (Rpop r)) ≤
              ∑ _r : Fin (t + 1), 64 * q ^ t := by
            apply Finset.sum_le_sum
            intro r hr
            by_cases hz : Fintype.card (Rpop r) = 0
            · omega
            · have hp : Nonempty (Rpop r) := Fintype.card_pos_iff.mp
                (Nat.pos_of_ne_zero hz)
              let x : Rpop r := Classical.choice hp
              have hUr : (U m f (r : Nat)).card > 0 := by
                apply Finset.card_pos.mpr
                refine ⟨bvec x.1, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
                exact le_of_eq x.2.2.1
              simpa [Rpop] using
                hpopular_child m f (r : Nat) (by omega) hUr
          _ = (t + 1) * (64 * q ^ t) := by simp
      calc
        Fintype.card Epop ≤ Fintype.card (Sigma Rpop) := hi
        _ ≤ (t + 1) * (64 * q ^ t) := hs
        _ = 64 * (t + 1) * q ^ t := by ring
    let Rpoor : Fin (t + 1) → Type := fun r =>
      {x : D.vertex // valid (m + 1) (Fin.snoc f x) ∧
        rnk m f (bvec x) = (r : Nat) ∧ poor m f (r : Nat) (avec x)}
    let Epoor : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧
      poor m f (rnk m f (bvec x)) (avec x)}
    let epoor : Epoor → Sigma Rpoor := fun x =>
      let r : Fin (t + 1) := ⟨rnk m f (bvec x.1),
        h_rank_lt_ext m f x.1 x.2.1⟩
      ⟨r, ⟨x.1, x.2.1, rfl, x.2.2⟩⟩
    have hepoor : Function.Injective epoor := by
      intro x y hxy
      dsimp [epoor] at hxy
      have hv : (x.1 : D.vertex) = y.1 := by
        simpa using congrArg (fun z : Sigma Rpoor => z.2.1) hxy
      exact Subtype.ext hv
    have hpoor_sum : Fintype.card Epoor ≤
        5000 * (t + 1) * q ^ t := by
      have hi : Fintype.card Epoor ≤ Fintype.card (Sigma Rpoor) :=
        Fintype.card_le_of_injective epoor hepoor
      have hs : Fintype.card (Sigma Rpoor) ≤
          (t + 1) * (5000 * q ^ t) := by
        rw [Fintype.card_sigma]
        calc
          (∑ r, Fintype.card (Rpoor r)) ≤
              ∑ _r : Fin (t + 1), 5000 * q ^ t := by
            apply Finset.sum_le_sum
            intro r hr
            by_cases hz : Fintype.card (Rpoor r) = 0
            · omega
            · have hp : Nonempty (Rpoor r) := Fintype.card_pos_iff.mp
                (Nat.pos_of_ne_zero hz)
              let x : Rpoor r := Classical.choice hp
              have hUr : (U m f (r : Nat)).card > 0 := by
                apply Finset.card_pos.mpr
                refine ⟨bvec x.1, Finset.mem_filter.mpr ⟨by simp, ?_⟩⟩
                exact le_of_eq x.2.2.1
              simpa [Rpoor] using
                hpoor_card m f (r : Nat) (by omega) hUr
          _ = (t + 1) * (5000 * q ^ t) := by simp
      calc
        Fintype.card Epoor ≤ Fintype.card (Sigma Rpoor) := hi
        _ ≤ (t + 1) * (5000 * q ^ t) := hs
        _ = 5000 * (t + 1) * q ^ t := by ring
    let X : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧ marked (m + 1) (Fin.snoc f x)}
    let e : X → Sum Epop Epoor := fun x =>
      if hp : popular m f (rnk m f (bvec x.1)) (bvec x.1) then
        Sum.inl ⟨x.1, x.2.1, hp⟩
      else
        Sum.inr ⟨x.1, x.2.1, by
          have hm : popular m f (rnk m f (bvec x.1)) (bvec x.1) ∨
              poor m f (rnk m f (bvec x.1)) (avec x.1) := by
            simpa [marked] using x.2.2
          exact hm.resolve_left hp⟩
    have he : Function.Injective e := by
      intro x y hxy
      have hm_x : popular m f (rnk m f (bvec x.1)) (bvec x.1) ∨
          poor m f (rnk m f (bvec x.1)) (avec x.1) := by
        simpa [marked] using x.2.2
      have hm_y : popular m f (rnk m f (bvec y.1)) (bvec y.1) ∨
          poor m f (rnk m f (bvec y.1)) (avec y.1) := by
        simpa [marked] using y.2.2
      by_cases hpx : popular m f (rnk m f (bvec x.1)) (bvec x.1)
      · have hpy : popular m f (rnk m f (bvec y.1)) (bvec y.1) := by
          by_contra hpy
          have hh : (Sum.inl ⟨x.1, x.2.1, hpx⟩ : Sum Epop Epoor) =
              Sum.inr ⟨y.1, y.2.1, hm_y.resolve_left hpy⟩ := by
            simpa [e, hpx, hpy] using hxy
          cases hh
        have hh : (⟨x.1, x.2.1, hpx⟩ : Epop) =
            ⟨y.1, y.2.1, hpy⟩ := by
          have hsum : (Sum.inl ⟨x.1, x.2.1, hpx⟩ : Sum Epop Epoor) =
              Sum.inl ⟨y.1, y.2.1, hpy⟩ := by
            simpa [e, hpx, hpy] using hxy
          exact Sum.inl.inj hsum
        exact Subtype.ext (congrArg (fun z : Epop => z.1) hh)
      · have hpy : ¬ popular m f (rnk m f (bvec y.1)) (bvec y.1) := by
          intro hpy
          have hh : (Sum.inr ⟨x.1, x.2.1, hm_x.resolve_left hpx⟩ : Sum Epop Epoor) =
              Sum.inl ⟨y.1, y.2.1, hpy⟩ := by
            simpa [e, hpx, hpy] using hxy
          cases hh
        have hh : (⟨x.1, x.2.1, hm_x.resolve_left hpx⟩ : Epoor) =
            ⟨y.1, y.2.1, hm_y.resolve_left hpy⟩ := by
          have hsum : (Sum.inr ⟨x.1, x.2.1, hm_x.resolve_left hpx⟩ :
              Sum Epop Epoor) = Sum.inr ⟨y.1, y.2.1, hm_y.resolve_left hpy⟩ := by
            simpa [e, hpx, hpy] using hxy
          exact Sum.inr.inj hsum
        exact Subtype.ext (congrArg (fun z : Epoor => z.1) hh)
    have hX : Fintype.card X ≤ Fintype.card Epop + Fintype.card Epoor := by
      calc
        Fintype.card X ≤ Fintype.card (Sum Epop Epoor) :=
          Fintype.card_le_of_injective e he
        _ = Fintype.card Epop + Fintype.card Epoor := by
          simp
    have hA' : 5064 * (t + 1) ≤ A := by
      have hconst : 5064 ≤ 20000 * t * t := by nlinarith [ht]
      exact (Nat.mul_le_mul_right (t + 1) hconst).trans hA
    calc
      Fintype.card X ≤ Fintype.card Epop + Fintype.card Epoor := hX
      _ ≤ 64 * (t + 1) * q ^ t + 5000 * (t + 1) * q ^ t := by
        exact Nat.add_le_add hpop_sum hpoor_sum
      _ = 5064 * (t + 1) * q ^ t := by ring
      _ ≤ A * q ^ t := Nat.mul_le_mul_right _ hA'
  have hW_mono : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex)
      (y : G.vertex), W m f y ≤ W (m + 1) (Fin.snoc f x) y := by
    intro m f x y
    apply Submodule.span_le.2
    intro v hv
    rcases Finset.mem_image.mp (show v ∈ S m f y from hv) with ⟨j, hj, hjv⟩
    apply Submodule.subset_span
    refine Finset.mem_image.mpr ⟨j.castSucc, ?_, ?_⟩
    · simpa using hj
    · simpa using hjv
  have hW_snoc_adj : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex)
      (y : G.vertex), G.adj (avec x) y →
      W (m + 1) (Fin.snoc f x) y =
        W m f y ⊔ Submodule.span K ({bvec' x} : Set V) := by
    intro m f x y
    intro hadjxy
    apply le_antisymm
    · apply Submodule.span_le.2
      intro v hv
      rcases Finset.mem_image.mp hv with ⟨i, hi, hvi⟩
      rw [← hvi]
      revert hi
      refine Fin.lastCases ?_ (fun j => ?_) i
      · intro hi
        have hnew : bvec' x ∈
            Submodule.span K ({bvec' x} : Set V) := by
          apply Submodule.subset_span
          simp
        exact (show Submodule.span K ({bvec' x} : Set V) ≤
            W m f y ⊔ Submodule.span K ({bvec' x} : Set V) from le_sup_right)
          (by simpa [Fin.snoc_last] using hnew)
      · intro hi
        have hold : bvec' (f j) ∈ W m f y := by
          apply Submodule.subset_span
          have hij : G.adj (avec (f j)) y := by
            simpa [Fin.snoc_castSucc] using hi
          refine Finset.mem_image.mpr
            ⟨j, Finset.mem_filter.mpr ⟨by simp, hij⟩, ?_⟩
          simp [Fin.snoc_castSucc]
        exact (show W m f y ≤
            W m f y ⊔ Submodule.span K ({bvec' x} : Set V) from le_sup_left)
          (by simpa [Fin.snoc_castSucc] using hold)
    · apply sup_le
      · apply Submodule.span_le.2
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨j, hj, hjv⟩
        apply Submodule.subset_span
        refine Finset.mem_image.mpr ⟨j.castSucc, ?_, ?_⟩
        · simpa using hj
        · simpa using hjv
      · apply Submodule.span_le.2
        intro v hv
        have hv' : v = bvec' x := by simpa using hv
        rw [hv']
        apply Submodule.subset_span
        refine Finset.mem_image.mpr ⟨Fin.last m, ?_, ?_⟩
        · exact Finset.mem_filter.mpr ⟨by simp, by simpa [Fin.snoc_last] using hadjxy⟩
        · simpa [Fin.snoc_last]
  have h_unmarked_decay : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex),
      valid (m + 1) (Fin.snoc f x) →
      ¬ marked (m + 1) (Fin.snoc f x) →
      ∃ l : Nat, l ≤ t ∧ (U m f l).card > 0 ∧
        ((U (m + 1) (Fin.snoc f x) l).card : ℝ) ≤
          (1 - 1 / (32 * (t : ℝ) * q)) * (U m f l).card := by
    intro m f x hx hxm
    let b := bvec x
    let a := avec x
    let r := rnk m f b
    have hrle : r ≤ t := by
      have hh := h_rank_lt_ext m f x hx
      have hh' : r < t + 1 := by simpa [r] using hh
      omega
    have hUr : (U m f r).card > 0 := by
      apply Finset.card_pos.mpr
      exact ⟨b, Finset.mem_filter.mpr ⟨by simp, by simp [r]⟩⟩
    let l := ell m f r
    have hel := hell m f r hUr
    have hlr : l ≤ r := by simpa [l] using hel.1
    have hZpos : (Z m f l).card > 0 := by
      simpa [l] using hell_mem_pos m f r hUr
    have hmark : ¬ (popular m f r b ∨ poor m f r a) := by
      intro hm
      apply hxm
      simpa [marked, b, a, r] using hm
    have hnpop : ¬ popular m f r b := fun hp => hmark (Or.inl hp)
    have hnpoor : ¬ poor m f r a := fun hp => hmark (Or.inr hp)
    let Zl := Z m f l
    let N := Zl.filter (fun y => G.adj a y)
    let Bad := Zl.filter (fun y => b.rep ∈ W m f y)
    let Y := Zl.filter (fun y => G.adj a y ∧ b.rep ∉ W m f y)
    have hbad : 16 * q * Bad.card < Zl.card := by
      have hnot := hnpop
      apply lt_of_not_ge
      intro hle
      apply hnot
      exact ⟨rfl, by simpa [Zl, l, Bad] using hle⟩
    have hn : Zl.card < 8 * q * N.card := by
      have hnot := hnpoor
      apply lt_of_not_ge
      intro hle
      apply hnot
      simpa [poor, l, Zl, N] using hle
    have hYeq : Y = N \ Bad := by
      ext y
      constructor
      · intro hy
        have hy' := Finset.mem_filter.mp hy
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_filter.mpr ⟨hy'.1, hy'.2.1⟩, ?_⟩
        intro hbad
        exact hy'.2.2 (Finset.mem_filter.mp hbad).2
      · intro hy
        have hy' := Finset.mem_sdiff.mp hy
        have hn := Finset.mem_filter.mp hy'.1
        apply Finset.mem_filter.mpr
        refine ⟨hn.1, hn.2, ?_⟩
        intro hbad
        apply hy'.2
        exact Finset.mem_filter.mpr ⟨hn.1, hbad⟩
    let J := N ∩ Bad
    have hcardN : N.card = Y.card + J.card := by
      have hh : (N \ Bad).card + (N ∩ Bad).card = N.card := by
        rw [← Finset.card_union_of_disjoint (Finset.disjoint_sdiff_inter N Bad),
          Finset.sdiff_union_inter]
      apply Eq.symm
      simpa only [hYeq, J] using hh
    have hJle : J.card ≤ Bad.card := by
      exact Finset.card_le_card Finset.inter_subset_right
    have hJmul : 8 * q * J.card ≤ 8 * q * Bad.card := by
      exact Nat.mul_le_mul_left (8 * q) hJle
    have hNrewrite : 8 * q * N.card =
        8 * q * Y.card + 8 * q * J.card := by
      rw [hcardN]
      ring
    rw [hNrewrite] at hn
    have hYlower : Zl.card ≤ 16 * q * Y.card := by
      nlinarith [hbad, hn, hJmul]
    have hYsub : Y ⊆ U m f l := by
      intro y hy
      have hyz := (Finset.mem_filter.mp hy).1
      have hyr := (Finset.mem_filter.mp hyz).2
      exact Finset.mem_filter.mpr ⟨by simp, le_of_eq hyr⟩
    have hUnsub : U (m + 1) (Fin.snoc f x) l ⊆
        U m f l \ Y := by
      intro y hy
      have hynew := (Finset.mem_filter.mp hy).2
      have hWmono : W m f y ≤ W (m + 1) (Fin.snoc f x) y := by
        exact hW_mono m f x y
      have hfin : rnk m f y ≤ rnk (m + 1) (Fin.snoc f x) y := by
        exact Submodule.finrank_mono hWmono
      have hyold : y ∈ U m f l := by
        apply Finset.mem_filter.mpr
        refine ⟨by simp, ?_⟩
        exact hfin.trans hynew
      have hynot : y ∉ Y := by
        intro hyY
        have hyz := (Finset.mem_filter.mp hyY).1
        have hyr : rnk m f y = l := (Finset.mem_filter.mp hyz).2
        have hnewrank : rnk (m + 1) (Fin.snoc f x) y = l + 1 := by
          have hnotW : bvec' x ∉ W m f y := by
            exact (Finset.mem_filter.mp hyY).2.2
          calc
            rnk (m + 1) (Fin.snoc f x) y =
                Module.finrank K ↥(W m f y ⊔ Submodule.span K ({bvec' x} : Set V)) := by
                    simpa [rnk] using congrArg
                      (fun S0 : Submodule K V => Module.finrank K S0)
                      (hW_snoc_adj m f x y
                        (Finset.mem_filter.mp hyY).2.1)
            _ = Module.finrank K ↥(W m f y) + 1 :=
              StrictSpanGrowth K V (W m f y) (bvec' x) hnotW
            _ = l + 1 := by simp [rnk, hyr]
        omega
      exact Finset.mem_sdiff.mpr ⟨hyold, hynot⟩
    have hcarddiff : (U m f l \ Y).card = (U m f l).card - Y.card :=
      Finset.card_sdiff_of_subset hYsub
    have hUnle := Finset.card_le_card hUnsub
    rw [hcarddiff] at hUnle
    have hsum : (U (m + 1) (Fin.snoc f x) l).card + Y.card ≤
        (U m f l).card := by
      have hYcard : Y.card ≤ (U m f l).card := Finset.card_le_card hYsub
      exact (Nat.le_sub_iff_add_le hYcard).mp hUnle
    let T : Finset Nat := Finset.range (r + 1)
    have hUeq : U m f r = T.biUnion (fun j => Z m f j) := by
      ext y
      constructor
      · intro hy
        have hyr := (Finset.mem_filter.mp hy).2
        apply Finset.mem_biUnion.mpr
        exact ⟨rnk m f y, by simp [T, hyr],
          Finset.mem_filter.mpr ⟨by simp, rfl⟩⟩
      · intro hy
        rcases Finset.mem_biUnion.mp hy with ⟨j, hj, hyj⟩
        have hjr : j ≤ r := by simpa [T] using hj
        exact Finset.mem_filter.mpr ⟨by simp,
          (Finset.mem_filter.mp hyj).2 ▸ hjr⟩
    have hdis : (↑T : Set Nat).PairwiseDisjoint (fun j => Z m f j) := by
      intro i hi j hj hij
      apply Finset.disjoint_left.2
      intro y hyi hyj
      have hiy := (Finset.mem_filter.mp hyi).2
      have hjy := (Finset.mem_filter.mp hyj).2
      exact hij (by omega)
    have hUle : (U m f l).card ≤ 2 * t * (Zl.card) := by
      have hUl : (U m f l).card ≤ (U m f r).card := by
        apply Finset.card_le_card
        intro y hy
        exact Finset.mem_filter.mpr ⟨by simp,
          (Finset.mem_filter.mp hy).2.trans (by omega)⟩
      have hsum : (U m f r).card = ∑ j ∈ T, (Z m f j).card := by
        rw [hUeq, Finset.card_biUnion hdis]
      have hparts : ∀ j ∈ T, (Z m f j).card ≤ Zl.card := by
        intro j hj
        exact (hel.2.2 j (by simpa [T] using hj))
      have hsumle : (∑ j ∈ T, (Z m f j).card) ≤
          ∑ _j ∈ T, Zl.card := Finset.sum_le_sum (fun j hj => hparts j hj)
      have hT : T.card ≤ 2 * t := by
        simp [T]
        omega
      calc
        (U m f l).card ≤ (U m f r).card := hUl
        _ = ∑ j ∈ T, (Z m f j).card := hsum
        _ ≤ ∑ _j ∈ T, Zl.card := hsumle
        _ = T.card * Zl.card := by simp
        _ ≤ 2 * t * Zl.card := by gcongr
    have hYreal : (Zl.card : ℝ) ≤ 16 * q * Y.card := by
      exact_mod_cast hYlower
    have hUreal : (U m f l).card ≤ 2 * (t : ℝ) * Zl.card := by
      exact_mod_cast hUle
    have hmulY := mul_le_mul_of_nonneg_left hYreal
      (show (0 : ℝ) ≤ 2 * t by positivity)
    have hUtoY : (U m f l).card ≤
        32 * (t : ℝ) * q * Y.card := by
      nlinarith [hUreal, hmulY]
    have hfrac : (U m f l).card / (32 * (t : ℝ) * q) ≤ Y.card := by
      apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * t * q)).2
      nlinarith [hUtoY]
    have hdec : ((U (m + 1) (Fin.snoc f x) l).card : ℝ) ≤
        (1 - 1 / (32 * (t : ℝ) * q)) * (U m f l).card := by
      have hsumR : ((U (m + 1) (Fin.snoc f x) l).card : ℝ) + Y.card ≤
          (U m f l).card := by exact_mod_cast hsum
      have hden : (0 : ℝ) < 32 * t * q := by positivity
      have hnew : ((U (m + 1) (Fin.snoc f x) l).card : ℝ) ≤
          (U m f l).card - Y.card := by
        linarith [hsumR]
      calc
        ((U (m + 1) (Fin.snoc f x) l).card : ℝ) ≤
            (U m f l).card - Y.card := hnew
        _ ≤ (U m f l).card -
            (U m f l).card / (32 * (t : ℝ) * q) := by
          linarith [hfrac]
        _ = (1 - 1 / (32 * (t : ℝ) * q)) * (U m f l).card := by ring
    have hUlpos : (U m f l).card > 0 := by
      rcases Finset.card_pos.mp hZpos with ⟨y, hy⟩
      apply Finset.card_pos.mpr
      exact ⟨y, Finset.mem_filter.mpr ⟨by simp,
        le_of_eq (Finset.mem_filter.mp hy).2⟩⟩
    exact ⟨l, by omega, hUlpos, hdec⟩
  let mark : ∀ m : Nat, ForwardIndependentTuple D m → Bool :=
    fun m σ => decide (marked m σ.vertex)
  have hmark_root : ∀ σ : ForwardIndependentTuple D 0, mark 0 σ = true := by
    intro σ
    simp [mark, marked]
  have hmark_child : ∀ (m : Nat) (σ : ForwardIndependentTuple D m),
      Nat.card {τ : ForwardIndependentTuple D (m + 1) //
        (∀ i : Fin m, τ.vertex i.castSucc = σ.vertex i) ∧
          mark (m + 1) τ = true} ≤ A * q ^ t := by
    intro m σ
    let f : Fin m → D.vertex := σ.vertex
    let X : Type := {x : D.vertex //
      valid (m + 1) (Fin.snoc f x) ∧ marked (m + 1) (Fin.snoc f x)}
    let Q : Type := {τ : ForwardIndependentTuple D (m + 1) //
      (∀ i : Fin m, τ.vertex i.castSucc = σ.vertex i) ∧ mark (m + 1) τ = true}
    letI : Fintype X := by dsimp [X]; infer_instance
    letI : Fintype Q := Fintype.ofFinite Q
    let e : Q → X := fun τ =>
      let x := τ.1.vertex (Fin.last m)
      have hfun : τ.1.vertex = Fin.snoc f x := by
        funext i
        refine Fin.lastCases (by simp [x]) (fun j => ?_) i
        simpa [f] using τ.2.1 j
      ⟨x, by
        have hv := valid_tuple (m + 1) τ.1
        rw [← hfun]
        exact hv,
        by
          have hm : marked (m + 1) τ.1.vertex := by
            apply of_decide_eq_true
            simpa [mark] using τ.2.2
          simpa [hfun] using hm⟩
    have he : Function.Injective e := by
      intro τ υ hxy
      have hlast : τ.1.vertex (Fin.last m) = υ.1.vertex (Fin.last m) :=
        congrArg Subtype.val hxy
      have hvertex : τ.1.vertex = υ.1.vertex := by
        have hτ : τ.1.vertex = Fin.snoc f (τ.1.vertex (Fin.last m)) := by
          funext i
          refine Fin.lastCases (by simp) (fun j => ?_) i
          simpa [f] using τ.2.1 j
        have hυ : υ.1.vertex = Fin.snoc f (υ.1.vertex (Fin.last m)) := by
          funext i
          refine Fin.lastCases (by simp) (fun j => ?_) i
          simpa [f] using υ.2.1 j
        rw [hτ, hυ, hlast]
      have tuple_ext : ∀ (a b : ForwardIndependentTuple D (m + 1)),
          a.vertex = b.vertex → a = b := by
        intro a b hab
        cases a with
        | mk av ai =>
          cases b with
          | mk bv bi =>
            dsimp at hab ⊢
            cases hab
            rfl
      apply Subtype.ext
      exact tuple_ext τ.1 υ.1 hvertex
    have hcard : Fintype.card Q ≤ Fintype.card X :=
      Fintype.card_le_of_injective e he
    have hraw := hmarked_raw m f
    have hnat : Fintype.card X ≤ A * q ^ t := by
      simpa only [X, f] using hraw
    have hq : Nat.card Q = Fintype.card Q := Nat.card_eq_fintype_card
    calc
      Nat.card Q = Fintype.card Q := hq
      _ ≤ Fintype.card X := hcard
      _ ≤ A * q ^ t := hnat
  have hU_mono : ∀ (m : Nat) (f : Fin m → D.vertex) (x : D.vertex)
      (l : Nat) (y : G.vertex),
      y ∈ U (m + 1) (Fin.snoc f x) l → y ∈ U m f l := by
    intro m f x l y hy
    have hWmono : W m f y ≤ W (m + 1) (Fin.snoc f x) y := by
      exact hW_mono m f x y
    have hfin : rnk m f y ≤ rnk (m + 1) (Fin.snoc f x) y :=
      Submodule.finrank_mono hWmono
    exact Finset.mem_filter.mpr ⟨by simp,
      hfin.trans (Finset.mem_filter.mp hy).2⟩
  refine ⟨mark, hmark_root, ?_, ?_⟩
  · intro m σ
    exact hmark_child m σ
  · intro m σ
    let pref : ∀ j : Nat, j ≤ m → ForwardIndependentTuple D j := fun j hj =>
      { vertex := fun i => σ.vertex ⟨i.val, by omega⟩
        independent := by
          intro i j hij
          exact σ.independent (by omega) }
    let nextEq : ∀ (i : Fin m),
        (pref (i.val + 1) (by omega)).vertex =
          Fin.snoc (pref i.val (by omega)).vertex (σ.vertex i) := fun i => by
      funext j
      refine Fin.lastCases (by simp [pref]) (fun h => ?_) j
      simp [pref]
    let u : Fin m → Prop := fun i =>
      mark (i.val + 1) (pref (i.val + 1) (by omega)) = false
    have hnext_valid : ∀ i : Fin m,
        valid (i.val + 1)
          (Fin.snoc (pref i.val (by omega)).vertex (σ.vertex i)) := by
      intro i
      have hv := valid_tuple (i.val + 1)
        (pref (i.val + 1) (by omega))
      rw [← nextEq i]
      exact hv
    have hdec_i : ∀ (i : Fin m), u i →
        ∃ l : Nat, l ≤ t ∧
          (U i.val (pref i.val (by omega)).vertex l).card > 0 ∧
          ((U (i.val + 1) (pref (i.val + 1) (by omega)).vertex l).card : ℝ) ≤
            (1 - 1 / (32 * (t : ℝ) * q)) *
              (U i.val (pref i.val (by omega)).vertex l).card := by
      intro i hi
      have hh := h_unmarked_decay i.val (pref i.val (by omega)).vertex
        (σ.vertex i) (by
          exact hnext_valid i) (by
            have hfalse : mark (i.val + 1) (pref (i.val + 1) (by omega)) = false := by
              simpa [u] using hi
            intro hm
            have hm' : marked (i.val + 1) (pref (i.val + 1) (by omega)).vertex := by
              rw [nextEq i]
              exact hm
            have htrue : mark (i.val + 1) (pref (i.val + 1) (by omega)) = true := by
              simp [mark, hm']
            exact Bool.noConfusion (hfalse.symm.trans htrue))
      simpa only [← nextEq i] using hh
    let psi : Fin m → Fin (t + 1) := fun i =>
      if hi : u i then
        ⟨Classical.choose (hdec_i i hi), by
          have hc := (Classical.choose_spec (hdec_i i hi)).1
          omega⟩
      else 0
    have hpsi_spec : ∀ (i : Fin m), u i →
        (U i.val (pref i.val (by omega)).vertex (psi i)).card > 0 ∧
          ((U (i.val + 1) (pref (i.val + 1) (by omega)).vertex (psi i)).card : ℝ) ≤
            (1 - 1 / (32 * (t : ℝ) * q)) *
              (U i.val (pref i.val (by omega)).vertex (psi i)).card := by
      intro i hi
      dsimp [psi]
      split
      next h =>
        exact ⟨(Classical.choose_spec (hdec_i i h)).2.1,
          (Classical.choose_spec (hdec_i i h)).2.2⟩
      next h => exact False.elim (h hi)
    let E : Finset (Fin m) := Finset.univ.filter (fun i => u i)
    have hE_mem (i : Fin m) : i ∈ E ↔ u i := by simp [E]
    let event (l : Fin (t + 1)) (i : Fin m) : Prop :=
      u i ∧ psi i = l
    let count (j : Nat) (l : Fin (t + 1)) : Nat :=
      (E.filter (fun i => i.val < j ∧ event l i)).card
    have hcount_succ : ∀ (j : Nat) (hj : j < m) (l : Fin (t + 1)),
        count (j + 1) l = count j l +
          (if event l ⟨j, hj⟩ then 1 else 0) := by
      intro j hj l
      let i : Fin m := ⟨j, hj⟩
      have hfilter : E.filter (fun z => z.val < j + 1 ∧ event l z) =
          E.filter (fun z => z.val < j ∧ event l z) ∪
            (if event l i then {i} else ∅) := by
        ext z
        by_cases hz : z = i
        · subst z
          simp only [Finset.mem_filter, Finset.mem_union]
          by_cases he : event l i
          · rw [if_pos he]
            simp only [Finset.mem_singleton]
            have hiE : i ∈ E := (hE_mem i).2 he.1
            have hlt : i.val < j + 1 := by
              dsimp [i]
              omega
            constructor
            · intro h
              exact Or.inr trivial
            · intro h
              exact ⟨hiE, hlt, he⟩
          · rw [if_neg he]
            constructor
            · intro h
              exact False.elim (he h.2.2)
            · intro h
              rcases h with h | h
              · exact False.elim (he h.2.2)
              · exact False.elim (by simpa using h)
        · by_cases he : event l i
          · simp only [Finset.mem_filter, Finset.mem_union]
            rw [if_pos he]
            simp only [Finset.mem_singleton]
            constructor
            · rintro ⟨hzE, hzlt, hzevent⟩
              by_cases hzj : z.val < j
              · exact Or.inl ⟨hzE, hzj, hzevent⟩
              · right
                exfalso
                apply hz
                apply Fin.ext
                change z.val = j
                omega
            · rintro (hz' | hz')
              · exact ⟨hz'.1, by omega, hz'.2.2⟩
              · exact False.elim (hz hz')
          · simp only [Finset.mem_filter, Finset.mem_union]
            rw [if_neg he]
            constructor
            · rintro ⟨hzE, hzlt, hzevent⟩
              by_cases hzj : z.val < j
              · exact Or.inl ⟨hzE, hzj, hzevent⟩
              · have hzi : z = i := by
                  apply Fin.ext
                  change z.val = j
                  omega
                exact False.elim (he (by simpa [hzi] using hzevent))
            · rintro (hz' | hz')
              · exact ⟨hz'.1, by omega, hz'.2.2⟩
              · exact False.elim (by simpa using hz')
      rw [show count (j + 1) l =
          (E.filter (fun z => z.val < j + 1 ∧ event l z)).card by rfl,
        hfilter, Finset.card_union_of_disjoint]
      · by_cases he : event l i <;> simp [i, he, count]
      · exact Finset.disjoint_left.mpr (by
          intro z hz1 hz2
          have hzlt := (Finset.mem_filter.mp hz1).2.1
          by_cases he : event l i
          · have hzi : z = i := by simpa [he] using hz2
            have hval : z.val = j := by
              simpa [i] using congrArg Fin.val hzi
            omega
          · simp [he] at hz2)
    have hgeom : ∀ (l : Fin (t + 1)) (j : Nat) (hj : j ≤ m),
        ((U j (pref j hj).vertex (l : Nat)).card : ℝ) ≤
          (n : ℝ) *
            (1 - 1 / (32 * (t : ℝ) * q)) ^ count j l := by
      intro l j
      induction j with
      | zero =>
          intro hj
          have hU0 : U 0 (pref 0 hj).vertex (l : Nat) =
              (Finset.univ : Finset G.vertex) := by
            ext y
            have hrank0 : rnk 0 (pref 0 hj).vertex y = 0 := by
              simp [rnk, W, S]
            simp [U, hrank0]
          rw [hU0]
          simp [count, E, event, u, pref, hGcard]
      | succ j ih =>
          intro hj
          have hjm : j < m := by omega
          let i : Fin m := ⟨j, hjm⟩
          have hmono : (U (j + 1) (pref (j + 1) hj).vertex (l : Nat)).card ≤
              (U j (pref j (by omega)).vertex (l : Nat)).card := by
            apply Finset.card_le_card
            intro y hy
            have h := hU_mono j (pref j (by omega)).vertex
              (σ.vertex i) (l : Nat) y
            rw [← nextEq i] at h
            exact h hy
          have hcnt := hcount_succ j hjm l
          by_cases he : event l i
          · have hu : u i := he.1
            have hps := hpsi_spec i hu
            have hps' : ((U (j + 1) (pref (j + 1) hj).vertex (l : Nat)).card : ℝ) ≤
                (1 - 1 / (32 * (t : ℝ) * q)) *
                    ((U j (pref j (by omega)).vertex (l : Nat)).card : ℝ) := by
              simpa [i, he.2] using hps.2
            have hc : 0 ≤ 1 - 1 / (32 * (t : ℝ) * q) := by
              have hden : 1 ≤ 32 * (t : ℝ) * q := by
                have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
                have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
                nlinarith
              have hh : (1 : ℝ) / (32 * (t : ℝ) * q) ≤ 1 := by
                apply (div_le_iff₀ (by positivity : (0 : ℝ) < 32 * t * q)).2
                nlinarith
              nlinarith
            calc
              ((U (j + 1) (pref (j + 1) hj).vertex (l : Nat)).card : ℝ) ≤
                  (1 - 1 / (32 * (t : ℝ) * q)) *
                    ((U j (pref j (by omega)).vertex (l : Nat)).card : ℝ) := hps'
              _ ≤ (1 - 1 / (32 * (t : ℝ) * q)) *
                    ((n : ℝ) * (1 - 1 / (32 * (t : ℝ) * q)) ^ count j l) := by
                gcongr
                exact ih (by omega)
              _ = (n : ℝ) *
                    (1 - 1 / (32 * (t : ℝ) * q)) ^ count (j + 1) l := by
                rw [hcnt, if_pos he, pow_succ]
                ring
          · calc
              ((U (j + 1) (pref (j + 1) hj).vertex (l : Nat)).card : ℝ) ≤
                  (U j (pref j (by omega)).vertex (l : Nat)).card := by
                exact_mod_cast hmono
              _ ≤ (n : ℝ) *
                    (1 - 1 / (32 * (t : ℝ) * q)) ^ count j l := ih (by omega)
              _ = (n : ℝ) *
                    (1 - 1 / (32 * (t : ℝ) * q)) ^ count (j + 1) l := by
                simp [hcnt, i, he]
    have hcount_total : (∑ l : Fin (t + 1), count m l) = E.card := by
      calc
        (Finset.univ.sum (fun l : Fin (t + 1) => count m l)) =
            Finset.univ.sum (fun l : Fin (t + 1) =>
              E.sum (fun i => if i.val < m ∧ event l i then 1 else 0)) := by
          apply Finset.sum_congr rfl
          intro l hl
          simp only [count, Finset.card_eq_sum_ones, Finset.sum_filter]
        _ = E.sum (fun i =>
              Finset.univ.sum (fun l : Fin (t + 1) =>
                if i.val < m ∧ event l i then 1 else 0)) := by
          rw [Finset.sum_comm]
        _ = E.sum (fun _i => 1) := by
          apply Finset.sum_congr rfl
          intro i hi
          have hui : u i := (hE_mem i).mp hi
          simp [event, hui, i.isLt]
        _ = E.card := by simp
    let L : Nat := Nat.log 2 q
    let N : Nat := 64 * t * t * q * L
    have hNtotal : (t + 1) * N ≤ A * q * L := by
      have hconst : 64 * t * t * (t + 1) ≤ A := by
        calc
          64 * t * t * (t + 1) ≤ 20000 * t * t * (t + 1) := by
            gcongr
            nlinarith
          _ ≤ A := hA
      calc
        (t + 1) * N = (64 * t * t * (t + 1)) * q * L := by
          simp [N]
          ring
        _ ≤ A * q * L := by gcongr
    have hsmall : (n : ℝ) *
          (1 - 1 / (32 * (t : ℝ) * q)) ^ N < 1 := by
      let rr : ℝ := 1 / (32 * (t : ℝ) * q)
      have hrr : 0 ≤ rr ∧ rr ≤ 1 := by
        constructor
        · dsimp [rr]
          positivity
        · dsimp [rr]
          have hden : 1 ≤ 32 * (t : ℝ) * q := by
            have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
            have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
            nlinarith
          apply (div_le_iff₀ (by positivity :
            (0 : ℝ) < 32 * t * q)).2
          nlinarith
      have hqlog : Real.log (q : ℝ) ≤ (L : ℝ) := by
        rcases hqpow with ⟨s, hs⟩
        have hLs : L = s := by
          dsimp [L]
          rw [hs, Nat.log_pow]
          omega
        have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
          have hlog2' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          nlinarith
        calc
          Real.log (q : ℝ) = Real.log ((2 : ℝ) ^ s) := by
            rw [hs]
            norm_num
          _ = s * Real.log (2 : ℝ) := by rw [Real.log_pow]
          _ ≤ (s : ℝ) := by nlinarith
          _ = (L : ℝ) := by rw [hLs]
      have hqt_exp : (q : ℝ) ^ t ≤ Real.exp ((t : ℝ) * L) := by
        calc
          (q : ℝ) ^ t = (Real.exp (Real.log (q : ℝ))) ^ t := by
            rw [Real.exp_log (by positivity)]
          _ = Real.exp ((t : ℝ) * Real.log (q : ℝ)) := by
            rw [← Real.exp_nat_mul]
          _ ≤ Real.exp ((t : ℝ) * L) := by
            apply Real.exp_le_exp.mpr
            gcongr
      have hqlogpos : 0 < L := by
        dsimp [L]
        exact Nat.log_pos (by omega) (by omega)
      have htl : Real.log (2 : ℝ) < (t : ℝ) * L := by
        have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
        have hLpos : (1 : ℝ) ≤ L := by
          exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hqlogpos))
        have hlog2 : Real.log (2 : ℝ) ≤ 1 := by
          have hlog2' := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
          nlinarith
        nlinarith
      have hrrN : (2 : ℝ) * t * L ≤ rr * (N : ℝ) := by
        dsimp [rr, N]
        norm_num [Nat.cast_mul, Nat.cast_pow]
        field_simp
        norm_num
      have hpowexp : (1 - rr) ^ N ≤ Real.exp (-rr * (N : ℝ)) := by
        calc
          (1 - rr) ^ N ≤ (Real.exp (-rr)) ^ N := by
            exact pow_le_pow_left₀ (a := 1 - rr) (b := Real.exp (-rr))
              (by linarith [hrr.2]) (Real.one_sub_le_exp_neg rr) _
          _ = Real.exp ((N : ℝ) * (-rr)) := by
            convert (Real.exp_nat_mul (-rr) N).symm using 1 <;> norm_num
          _ = Real.exp (-rr * (N : ℝ)) := by
            congr 1
            ring
      have hsmall_exp : Real.exp (-rr * (N : ℝ)) ≤
          Real.exp (-2 * (t : ℝ) * L) := by
        apply Real.exp_le_exp.mpr
        linarith [hrrN]
      have hhalf : Real.exp (-((t : ℝ) * L)) < (1 / 2 : ℝ) := by
        have hh := Real.exp_lt_exp.mpr (show -((t : ℝ) * L) < -Real.log 2 by
          linarith [htl])
        have hh' : Real.exp (-Real.log (2 : ℝ)) = (1 / 2 : ℝ) := by
          rw [Real.exp_neg, Real.exp_log (by norm_num)]
          norm_num
        rw [hh'] at hh
        exact hh
      have hfinal : (2 : ℝ) * Real.exp (-((t : ℝ) * L)) < 1 := by
        nlinarith [hhalf]
      calc
        (n : ℝ) * (1 - 1 / (32 * (t : ℝ) * q)) ^ N =
            (n : ℝ) * (1 - rr) ^ N := by rfl
        _ ≤ (n : ℝ) * Real.exp (-rr * (N : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hpowexp (by positivity)
        _ ≤ (n : ℝ) * Real.exp (-2 * (t : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_left hsmall_exp (by positivity)
        _ ≤ 2 * (q : ℝ) ^ t * Real.exp (-2 * (t : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_right hnhigh (by positivity)
        _ ≤ 2 * Real.exp ((t : ℝ) * L) *
              Real.exp (-2 * (t : ℝ) * L) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hqt_exp (by norm_num)) (by positivity)
        _ = 2 * Real.exp (-((t : ℝ) * L)) := by
          calc
            2 * Real.exp ((t : ℝ) * L) * Real.exp (-2 * (t : ℝ) * L) =
                2 * (Real.exp ((t : ℝ) * L) *
                  Real.exp (-2 * (t : ℝ) * L)) := by ring
            _ = 2 * Real.exp ((t : ℝ) * L + (-2 * (t : ℝ) * L)) := by
              rw [Real.exp_add]
            _ = 2 * Real.exp (-((t : ℝ) * L)) := by
              congr 1
              ring_nf
        _ < 1 := hfinal
    by_contra hnot
    have hsum_u : (∑ i : Fin m, if u i then 1 else 0) = E.card := by
      simpa [E] using
        (Finset.sum_boole (R := Nat) (fun i : Fin m => u i)
          (Finset.univ : Finset (Fin m)))
    have hsum_mark :
        (∑ i : Fin m,
          if mark (i.val + 1) (pref (i.val + 1) (by omega)) = false then 1 else 0) =
          E.card := by
      change (∑ i : Fin m, if u i then 1 else 0) = E.card
      exact hsum_u
    have hnotE : ¬ E.card ≤ A * q * L := by
      intro hE
      apply hnot
      rw [hsum_mark]
      simpa [L] using hE
    have hlarge : A * q * L < E.card := by
      exact Nat.lt_of_not_ge hnotE
    have hexists : ∃ l : Fin (t + 1), N < count m l := by
      by_contra hno
      push_neg at hno
      have hsumle : (∑ l : Fin (t + 1), count m l) ≤
          ∑ _l : Fin (t + 1), N := Finset.sum_le_sum (fun l _ => hno l)
      have hsumN : (∑ _l : Fin (t + 1), N) = (t + 1) * N := by simp
      rw [hcount_total] at hsumle
      have hEbound : E.card ≤ (t + 1) * N := by simpa [hsumN] using hsumle
      have htotal : E.card ≤ A * q * L := hEbound.trans hNtotal
      omega
    rcases hexists with ⟨l0, hl0⟩
    let El : Finset (Fin m) := E.filter (event l0)
    have hElcard : El.card = count m l0 := by
      change (E.filter (event l0)).card =
        (E.filter (fun i => i.val < m ∧ event l0 i)).card
      apply congrArg Finset.card
      ext i
      by_cases hi : i ∈ E
      · simp [hi, i.isLt]
      · simp [hi]
    have hElpos : El.Nonempty := by
      apply Finset.card_pos.mp
      rw [hElcard]
      omega
    let imax : Fin m := El.max' hElpos
    have himax : imax ∈ El := Finset.max'_mem El hElpos
    have hEl_eq : El.filter (fun i => i.val < imax.val) = El.erase imax := by
      ext i
      by_cases hii : i = imax
      · subst i
        simp
      · simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨hiEl, hilt⟩
          exact ⟨hii, hiEl⟩
        · rintro ⟨hine, hiEl⟩
          have hle := Finset.le_max' El i hiEl
          have hneq : i.val ≠ imax.val := by
            intro heq
            apply hii
            exact Fin.ext heq
          exact ⟨hiEl, by omega⟩
    have hcountpre : N ≤ count imax.val l0 := by
      have heq : count imax.val l0 =
          (El.filter (fun i => i.val < imax.val)).card := by
        unfold count
        dsimp [El]
        apply congrArg Finset.card
        ext i
        by_cases hiE : i ∈ E
        · simp only [Finset.mem_filter]
          constructor
          · rintro ⟨_, hilt, hev⟩
            exact ⟨⟨hiE, hev⟩, hilt⟩
          · rintro ⟨⟨_, hev⟩, hilt⟩
            exact ⟨hiE, hilt, hev⟩
        · simp [hiE]
      rw [heq, hEl_eq, Finset.card_erase_of_mem himax]
      omega
    have himax_event : event l0 imax := (Finset.mem_filter.mp himax).2
    have hps := hpsi_spec imax himax_event.1
    have hpos : (U imax.val (pref imax.val (by omega)).vertex (l0 : Nat)).card > 0 := by
      simpa [himax_event.2] using hps.1
    have hg := hgeom l0 imax.val (by omega)
    have hdenpos : 0 < (32 : ℝ) * t * q := by positivity
    have hc0 : 0 ≤ 1 - 1 / ((32 : ℝ) * t * q) := by
      have hden : 1 ≤ (32 : ℝ) * t * q := by
        have ht' : (2 : ℝ) ≤ t := by exact_mod_cast ht
        have hq' : (16 : ℝ) ≤ q := by exact_mod_cast hq
        nlinarith
      have hh : (1 : ℝ) / ((32 : ℝ) * t * q) ≤ 1 := by
        apply (div_le_iff₀ hdenpos).2
        nlinarith
      nlinarith
    have hc1 : 1 - 1 / ((32 : ℝ) * t * q) ≤ 1 := by
      have : 0 ≤ (1 : ℝ) / ((32 : ℝ) * t * q) := by positivity
      nlinarith
    have hpowcount :
        (1 - 1 / ((32 : ℝ) * t * q)) ^ count imax.val l0 ≤
          (1 - 1 / ((32 : ℝ) * t * q)) ^ N :=
      pow_le_pow_of_le_one hc0 hc1 hcountpre
    have hltone :
        ((U imax.val (pref imax.val (by omega)).vertex (l0 : Nat)).card : ℝ) < 1 := by
      calc
        ((U imax.val (pref imax.val (by omega)).vertex (l0 : Nat)).card : ℝ) ≤
            (n : ℝ) * (1 - 1 / ((32 : ℝ) * t * q)) ^ count imax.val l0 := hg
        _ ≤ (n : ℝ) * (1 - 1 / ((32 : ℝ) * t * q)) ^ N := by
          exact mul_le_mul_of_nonneg_left hpowcount (by positivity)
        _ < 1 := hsmall
    have hzero : (U imax.val (pref imax.val (by omega)).vertex (l0 : Nat)).card = 0 := by
      have hnatlt : (U imax.val (pref imax.val (by omega)).vertex (l0 : Nat)).card < 1 := by
        exact_mod_cast hltone
      omega
    omega
