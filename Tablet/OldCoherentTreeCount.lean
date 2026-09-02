import Tablet.OldPairDigraph
import Tablet.OldPolarityParameters
import Tablet.ForwardIndependentCount
import Tablet.ForwardIndependentTuple
import Tablet.RootedTreeCounting
import Tablet.AlonRodlBound

open scoped BigOperators

set_option maxHeartbeats 1000000

-- [TABLET NODE: OldCoherentTreeCount]
theorem OldCoherentTreeCount
    (K : Type) [Field K] [Fintype K]
    (t q k : Nat) (hqpow : IsPrimePow q) (hq : 16 ≤ q)
    (hK : Fintype.card K = q) (ht : 2 ≤ t) :
    let G := PolarityGraph K t ht
    letI : Fintype G.vertex := G.fintype
    letI : DecidableRel G.adj := G.decidableAdj
    ∀ (n d : Nat) (lambda : ℝ),
      (@Fintype.card G.vertex G.fintype = n ∧
        n = (q ^ (t + 1) - 1) / (q - 1) ∧
        d = (q ^ t - 1) / (q - 1) ∧
        (∀ v : G.vertex, Fintype.card {u : G.vertex // G.adj v u} = d) ∧
        lambda = Real.sqrt ((d : ℝ) -
          ((((q ^ (t - 1) - 1) / (q - 1) : Nat) : ℝ))) ∧
        NonprincipalSpectralBound G lambda ∧
        (q : ℝ) ^ t / 2 ≤ n ∧ (n : ℝ) ≤ 2 * (q : ℝ) ^ t ∧
        (q : ℝ) ^ (t - 1) / 2 ≤ d ∧
        (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) ∧
        lambda ≤ 2 * Real.sqrt d) →
      (∀ A B : Finset G.vertex,
        |((A.product B).filter (fun e => G.adj e.1 e.2)).card -
            (d : ℝ) / n * A.card * B.card| ≤
          lambda * Real.sqrt (A.card * B.card)) →
      0 < n → 0 < d →
      32 * t * q * Nat.ceil (Real.log (q : ℝ)) ≤ k →
      (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
        (8 : ℝ) ^ k * (lambda ^ 2 / d ^ 2) ^
            (k - 32 * t * q * Nat.ceil (Real.log (q : ℝ))) *
          (n : ℝ) ^ (2 * k) := by
-- BODY
  dsimp
  intro n d lambda hp hmix hn hd hw
  classical
  rcases hp with ⟨hcard, hnform, hdform, hdeg, hlam, hspectral,
    hnlow, hnhigh, hdlow, hdhigh, hlamhigh⟩
  let G : LoopGraph := PolarityGraph K t ht
  letI : Fintype G.vertex := G.fintype
  letI : DecidableRel G.adj := G.decidableAdj
  let D : LooplessDigraph := OldPairDigraph G
  letI : Fintype D.vertex := D.fintype
  letI : DecidableRel D.arc := D.decidableArc
  let valid : ∀ m : Nat, (Fin m → D.vertex) → Prop := fun m f =>
    ∀ ⦃i j : Fin m⦄, i.val < j.val → ¬ D.arc (f i) (f j)
  let pre : ∀ {m : Nat}, (Fin m → D.vertex) → (i : Fin m) →
      (Fin i → D.vertex) := fun {m} f i j =>
    f (Fin.castLT j (lt_trans j.isLt i.isLt))
  let Bset : ∀ {m : Nat}, (Fin m → D.vertex) → Finset G.vertex :=
    fun {m} f => Finset.univ.filter (fun b =>
      ∀ i : Fin m, ¬ G.adj ((f i).1.1) b)
  let Aset : ∀ {m : Nat}, (Fin m → D.vertex) → Finset G.vertex :=
    fun {m} f => Finset.univ.filter (fun a =>
      (((Bset f).filter (fun b => G.adj a b)).card : ℝ) ≤
        (d : ℝ) * (Bset f).card / (2 * n))
  let unmarked : ∀ {m : Nat}, (Fin m → D.vertex) → D.vertex → Prop :=
    fun {m} f x =>
      ¬ (x.1.1 ∈ Aset f ∧ x.1.2 ∈ Bset f)
  have valid_snoc_iff {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      valid (m + 1) (Fin.snoc f x) ↔
        valid m f ∧ ∀ i : Fin m, ¬ D.arc (f i) x := by
    constructor
    · intro h
      constructor
      · intro i j hij
        simpa [Fin.snoc_castSucc] using
          h (i := i.castSucc) (j := j.castSucc) (by simpa using hij)
      · intro i
        simpa [Fin.snoc_castSucc, Fin.snoc_last] using
          h (i := i.castSucc) (j := Fin.last m) (by simpa using i.isLt)
    · rintro ⟨hf, hx⟩ i j hij
      revert hij
      revert j
      refine Fin.lastCases ?_ (fun i => ?_) i
      · intro j hij
        exfalso
        simp [Fin.last] at hij
        omega
      · intro j
        refine Fin.lastCases ?_ (fun j => ?_) j
        · intro hij
          simpa [Fin.snoc_castSucc, Fin.snoc_last] using hx i
        · intro hij
          have : i.val < j.val := by simpa using hij
          simpa [Fin.snoc_castSucc] using hf this
  have pre_snoc {m : Nat} (f : Fin m → D.vertex) (x : D.vertex)
      (i : Fin m) : pre (Fin.snoc f x) i.castSucc = pre f i := by
    funext j
    simp only [pre]
    let u : Fin m := Fin.castLT j (lt_trans j.isLt i.isLt)
    have hu : Fin.castLT j (lt_trans j.isLt i.castSucc.isLt) = u.castSucc := by
      apply Fin.ext
      rfl
    rw [hu, Fin.snoc_castSucc]
  have pre_snoc_last {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      pre (Fin.snoc f x) (Fin.last m) = f := by
    funext j
    simp only [pre]
    let u : Fin m := ⟨j.val, j.isLt⟩
    rw [show Fin.castLT j (lt_trans j.isLt (Fin.last m).isLt) = u.castSucc by
          apply Fin.ext
          rfl]
    rw [Fin.snoc_castSucc]
    congr 1
  have unmarked_snoc {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      unmarked (pre (Fin.snoc f x) (Fin.last m)) x ↔ unmarked f x := by
    simp only [pre_snoc_last]
  let H : ℝ := 4 * lambda ^ 2 / d ^ 2 * n ^ 2
  let h : Nat := ⌊H⌋₊
  have hGcard : Fintype.card G.vertex = n := by
    simpa [G] using hcard
  have hDcard : Fintype.card D.vertex ≤ n ^ 2 := by
    let e : D.vertex → G.vertex × G.vertex := fun x => x.1
    have he : Function.Injective e := by
      intro x y hxy
      exact Subtype.ext hxy
    have hh := Fintype.card_le_of_injective e he
    simpa [D, Fintype.card_prod, hGcard, pow_two] using hh
  have hA_low {m : Nat} (f : Fin m → D.vertex) :
      ∀ a ∈ Aset f,
        (((Bset f).filter (fun b => G.adj a b)).card : ℝ) ≤
          (d : ℝ) * (Bset f).card / (2 * n) := by
    intro a ha
    exact (Finset.mem_filter.mp ha).2
  have hAB {m : Nat} (f : Fin m → D.vertex) :
      (Aset f).card * (Bset f).card ≤ h := by
    have hh := AlonRodlBound G.adj n d lambda hGcard hmix hn hd
      (Aset f) (Bset f) (hA_low f)
    have hh' : ((Aset f).card : ℝ) * (Bset f).card ≤ H := by
      simpa [H] using hh
    exact Nat.le_floor (by simpa using hh')
  have hmarked {m : Nat} (f : Fin m → D.vertex) :
      Fintype.card {x : D.vertex // ¬ unmarked f x ∧
        valid (m + 1) (Fin.snoc f x)} ≤ h := by
    let e : {x : D.vertex // ¬ unmarked f x ∧
        valid (m + 1) (Fin.snoc f x)} →
        (Aset f) × (Bset f) := fun x => by
      have hmark : x.1.1.1 ∈ Aset f ∧ x.1.1.2 ∈ Bset f := by
        simpa [unmarked] using x.2.1
      exact ⟨⟨x.1.1.1, hmark.1⟩, ⟨x.1.1.2, hmark.2⟩⟩
    have he : Function.Injective e := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · exact congrArg (fun z => z.1.1) hxy
      · exact congrArg (fun z => z.2.1) hxy
    have hc := Fintype.card_le_of_injective e he
    have hc' : Fintype.card {x : D.vertex // ¬ unmarked f x ∧
        valid (m + 1) (Fin.snoc f x)} ≤ (Aset f).card * (Bset f).card := by
      simpa using hc
    exact hc'.trans (hAB f)
  let sig : ∀ {m : Nat}, (Fin m → D.vertex) → (i : Fin m) → Bool :=
    fun {m} f i => decide (unmarked (pre f i) (f i))
  let weight : ∀ {m : Nat}, (Fin m → Bool) → Nat :=
    fun {m} z => ∑ i, if z i = true then 1 else 0
  have Bset_snoc {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      Bset (Fin.snoc f x) = (Bset f).filter (fun b => ¬ G.adj x.1.1 b) := by
    ext b
    simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro hb
      constructor
      · intro i
        simpa [Fin.snoc_castSucc] using hb i.castSucc
      · simpa [Fin.snoc_last] using hb (Fin.last m)
    · rintro ⟨hb, hx⟩ i
      refine Fin.lastCases ?_ (fun j => ?_) i
      · simpa [Fin.snoc_last] using hx
      · simpa [Fin.snoc_castSucc] using hb j
  have pre_init {m : Nat} (f : Fin (m + 1) → D.vertex) (i : Fin m) :
      pre f i.castSucc = pre (Fin.init f) i := by
    calc
      pre f i.castSucc =
          pre (Fin.snoc (Fin.init f) (f (Fin.last m))) i.castSucc := by
            rw [Fin.snoc_init_self]
      _ = pre (Fin.init f) i := pre_snoc _ _ i
  have pre_last_init {m : Nat} (f : Fin (m + 1) → D.vertex) :
      pre f (Fin.last m) = Fin.init f := by
    calc
      pre f (Fin.last m) =
          pre (Fin.snoc (Fin.init f) (f (Fin.last m))) (Fin.last m) := by
            rw [Fin.snoc_init_self]
      _ = Fin.init f := pre_snoc_last _ _
  have sig_snoc_castSucc {m : Nat} (f : Fin m → D.vertex) (x : D.vertex)
      (i : Fin m) : sig (Fin.snoc f x) i.castSucc = sig f i := by
    simp only [sig, pre_snoc, Fin.snoc_castSucc]
  have sig_snoc_last {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      sig (Fin.snoc f x) (Fin.last m) = decide (unmarked f x) := by
    simp only [sig, pre_snoc_last, Fin.snoc_last]
  have weight_snoc {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      weight (sig (Fin.snoc f x)) = weight (sig f) +
        (if unmarked f x then 1 else 0) := by
    simp only [weight, Fin.sum_univ_castSucc, sig_snoc_castSucc, sig_snoc_last]
    by_cases hu : unmarked f x <;> simp [hu]
  let r : ℝ := (d : ℝ) / (2 * n)
  have hBsubset {m : Nat} (f : Fin m → D.vertex) (x : D.vertex) :
      (Bset (Fin.snoc f x)).card ≤ (Bset f).card := by
    rw [Bset_snoc]
    exact Finset.card_filter_le _ _
  have hBdecay {m : Nat} (f : Fin m → D.vertex) (x : D.vertex)
      (hf : valid m f) (hx : valid (m + 1) (Fin.snoc f x))
      (hu : unmarked f x) :
      ((Bset (Fin.snoc f x)).card : ℝ) <
        (1 - r) * (Bset f).card := by
    have hxb : x.1.2 ∈ Bset f := by
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      have hno := (valid_snoc_iff f x).mp hx |>.2 i
      simpa [D, OldPairDigraph] using hno
    have hxa : x.1.1 ∉ Aset f := by
      intro ha
      exact hu ⟨ha, hxb⟩
    let Nset : Finset G.vertex := (Bset f).filter (fun b => G.adj x.1.1 b)
    have hN : ¬ (Nset.card : ℝ) ≤ (d : ℝ) * (Bset f).card / (2 * n) := by
      intro hle
      apply hxa
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [Nset] using hle⟩
    have hN' : r * (Bset f).card < Nset.card := by
      have hlt := lt_of_not_ge hN
      calc
        r * (Bset f).card = (d : ℝ) * (Bset f).card / (2 * n) := by
          dsimp [r]
          ring
        _ < Nset.card := hlt
    have hpart : Nset.card +
        ((Bset f).filter (fun b => ¬ G.adj x.1.1 b)).card = (Bset f).card := by
      simpa [Nset] using
        (Finset.card_filter_add_card_filter_not
          (s := Bset f) (fun b => G.adj x.1.1 b))
    have hpartR : (Nset.card : ℝ) +
        ((Bset f).filter (fun b => ¬ G.adj x.1.1 b)).card =
          (Bset f).card := by
      exact_mod_cast hpart
    have hnext : ((Bset f).filter (fun b => ¬ G.adj x.1.1 b)).card =
        (Bset f).card - Nset.card := by
      have hpart' := congrArg (fun z : Nat => z - Nset.card) hpart
      omega
    rw [Bset_snoc, hnext]
    have hNle : Nset.card ≤ (Bset f).card := by
      exact Finset.card_le_card (Finset.filter_subset _ _)
    rw [Nat.cast_sub hNle]
    have hrnonneg : 0 ≤ r := by
      dsimp [r]
      positivity
    nlinarith [hpartR, hN']
  have hqR : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqR
  have hqpowpos : ∀ m : Nat, 0 < (q : ℝ) ^ m := by
    intro m
    positivity
  have hpowstep : (q : ℝ) ^ (t - 1) * q = (q : ℝ) ^ t := by
    rw [← pow_succ]
    congr 1
    omega
  have hpowlower : 16 * (q : ℝ) ^ (t - 1) ≤ (q : ℝ) ^ t := by
    calc
      16 * (q : ℝ) ^ (t - 1) ≤ q * (q : ℝ) ^ (t - 1) := by
        exact mul_le_mul_of_nonneg_right hqR (by positivity)
      _ = (q : ℝ) ^ (t - 1) * q := by ring
      _ = (q : ℝ) ^ t := hpowstep
  have hd_le_n : (d : ℝ) ≤ n := by
    have hd' : (d : ℝ) ≤ 2 * (q : ℝ) ^ (t - 1) := by
      exact hdhigh
    have hn' : (q : ℝ) ^ t / 2 ≤ n := hnlow
    nlinarith [hpowlower]
  have hrange : 0 ≤ r ∧ r ≤ 1 := by
    constructor
    · dsimp [r]
      positivity
    · apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * n)).2
      nlinarith [hd_le_n]
  have hratio : 1 / (8 * (q : ℝ)) ≤ r := by
    have hd' : (q : ℝ) ^ (t - 1) / 2 ≤ d := hdlow
    have hn' : (n : ℝ) ≤ 2 * (q : ℝ) ^ t := hnhigh
    have hqd : (q : ℝ) ^ (t - 1) ≤ 2 * d := by nlinarith [hd']
    have hqt : (q : ℝ) ^ t ≤ 2 * q * d := by
      calc
        (q : ℝ) ^ t = (q : ℝ) ^ (t - 1) * q := hpowstep.symm
        _ ≤ (2 * d) * q := by gcongr
        _ = 2 * q * d := by ring
    have hnd : (n : ℝ) ≤ 4 * q * d := by
      calc
        n ≤ 2 * (q : ℝ) ^ t := hn'
        _ ≤ 2 * (2 * q * d) := by gcongr
        _ = 4 * q * d := by ring
    rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 8 * q)
      (by positivity : (0 : ℝ) < 2 * n)]
    nlinarith [hnd]
  have decay : ∀ m : Nat, ∀ f : Fin m → D.vertex, valid m f →
      ((Bset f).card : ℝ) ≤ (n : ℝ) *
        (1 - r) ^ (weight (sig f)) := by
    intro m
    induction m with
    | zero =>
        intro f hf
        have hf0 : f = (fun i : Fin 0 => Fin.elim0 i) := by
          funext i
          exact Fin.elim0 i
        simp [hf0, Bset, hGcard, weight, sig]
    | succ m ih =>
        intro f hf
        let p : Fin m → D.vertex := Fin.init f
        let x : D.vertex := f (Fin.last m)
        have hpvalid : valid m p := by
          intro i j hij
          exact hf (i := i.castSucc) (j := j.castSucc) (by simpa using hij)
        have hxf : f = Fin.snoc p x := by
          exact (Fin.snoc_init_self f).symm
        have hnextvalid : valid (m + 1) (Fin.snoc p x) := by
          rw [← hxf]
          exact hf
        have hprev := ih p hpvalid
        rw [hxf, Bset_snoc]
        by_cases hu : unmarked p x
        · have hstrict := hBdecay p x hpvalid hnextvalid hu
          have hstrict' : ((Bset p).filter (fun b => ¬G.adj x.1.1 b)).card <
              (1 - r) * (Bset p).card := by
            rw [← Bset_snoc]
            exact hstrict
          rw [weight_snoc p x]
          simp [hu]
          have hcalc : (((Bset p).filter (fun b => ¬G.adj x.1.1 b)).card : ℝ) <
              (n : ℝ) * (1 - r) ^ (weight (sig p) + 1) := by
            calc
            (((Bset p).filter (fun b => ¬G.adj x.1.1 b)).card : ℝ) <
                (1 - r) * (Bset p).card := hstrict'
            _ ≤ (1 - r) * ((n : ℝ) * (1 - r) ^ weight (sig p)) := by
              gcongr
              exact sub_nonneg.mpr hrange.2
            _ = (n : ℝ) * (1 - r) ^ (weight (sig p) + 1) := by
              rw [pow_add]
              ring
          exact hcalc.le
        · have hsubset := hBsubset p x
          have hsubset' : ((Bset p).filter (fun b => ¬G.adj x.1.1 b)).card ≤
              (Bset p).card := by
            simpa [Bset_snoc] using hsubset
          rw [weight_snoc p x]
          simp [hu]
          calc
            (((Bset p).filter (fun b => ¬G.adj x.1.1 b)).card : ℝ) ≤
                (Bset p).card := by exact_mod_cast hsubset'
            _ ≤ (n : ℝ) * (1 - r) ^ weight (sig p) := hprev
  let Path : Nat → Type := fun m => {f : Fin m → D.vertex // valid m f}
  let Ext : ∀ m : Nat, Path m → Type := fun m p =>
    {x : D.vertex // valid (m + 1) (Fin.snoc p.1 x)}
  have path_succ_equiv (m : Nat) :
      Path (m + 1) ≃ Σ p : Path m, Ext m p := by
    let toFun : Path (m + 1) → Σ p : Path m, Ext m p := fun z =>
      ⟨⟨Fin.init z.1, by
        intro i j hij
        exact z.2 (i := i.castSucc) (j := j.castSucc) (by simpa using hij)⟩,
        ⟨z.1 (Fin.last m), by
          simpa only [Fin.snoc_init_self] using z.2⟩⟩
    let invFun : (Σ p : Path m, Ext m p) → Path (m + 1) := fun z =>
      ⟨Fin.snoc z.1.1 z.2.1, z.2.2⟩
    have left_inv (z : Path (m + 1)) : invFun (toFun z) = z := by
      apply Subtype.ext
      exact Fin.snoc_init_self z.1
    have right_inv (z : Σ p : Path m, Ext m p) : toFun (invFun z) = z := by
      rcases z with ⟨p, x⟩
      have hp : (toFun (invFun (⟨p, x⟩))).1 = p := by
        apply Subtype.ext
        exact Fin.init_snoc (α := fun _ : Fin (m + 1) => D.vertex) x.1 p.1
      apply Sigma.ext_iff.mpr
      refine ⟨hp, ?_⟩
      have cast_ext_val {p q : Path m} (h : p = q) (a : Ext m p) :
          ((cast (congrArg (fun u : Path m => Ext m u) h) a : Ext m q) : D.vertex) = a.1 := by
        cases h
        rfl
      exact heq_of_cast_eq
        (congrArg (fun u : Path m => Ext m u) hp) (by
          apply Subtype.ext
          calc
            ((cast (congrArg (fun u : Path m => Ext m u) hp)
                (toFun (invFun (⟨p, x⟩))).2 : Ext m p) : D.vertex) =
                ((toFun (invFun (⟨p, x⟩))).2 : D.vertex) := cast_ext_val hp _
            _ = x.1 := by
              change (Fin.snoc (α := fun _ : Fin (m + 1) => D.vertex) p.1 x.1)
                (Fin.last m) = x.1
              exact Fin.snoc_last _ _)
    exact Equiv.mk toFun invFun left_inv right_inv
  let L : Nat := Nat.ceil (Real.log (q : ℝ))
  let W : Nat := 32 * t * q * L
  have hWk : W ≤ k := by simpa [W, L] using hw
  have hqR' : (16 : ℝ) ≤ q := by exact_mod_cast hq
  have hqpos' : (0 : ℝ) < q := lt_of_lt_of_le (by norm_num) hqR'
  have hLpos : 0 < L := by
    apply (Nat.ceil_pos).2
    exact Real.log_pos (by nlinarith [hqpos'])
  have hlog2q : Real.log (2 : ℝ) < Real.log (q : ℝ) := by
    apply Real.strictMonoOn_log
    · norm_num
    · exact hqpos'
    · nlinarith [hqR']
  have hLlog : Real.log (q : ℝ) ≤ (L : ℝ) := by
    exact Nat.le_ceil _
  have hlog2L : Real.log (2 : ℝ) < (L : ℝ) := hlog2q.trans_le hLlog
  have htpos : (1 : ℝ) ≤ t := by exact_mod_cast (show 1 ≤ t by omega)
  have htl : Real.log (2 : ℝ) < (t : ℝ) * L := by
    have hnonneg : 0 ≤ ((t : ℝ) - 1) * (L : ℝ) := by
      positivity
    nlinarith [hlog2L]
  have hqt_exp : (q : ℝ) ^ t ≤ Real.exp ((t : ℝ) * L) := by
    calc
      (q : ℝ) ^ t = (Real.exp (Real.log (q : ℝ))) ^ t := by
        rw [Real.exp_log hqpos']
      _ = Real.exp ((t : ℝ) * Real.log (q : ℝ)) := by
        rw [← Real.exp_nat_mul]
      _ ≤ Real.exp ((t : ℝ) * L) := by
        apply Real.exp_le_exp.mpr
        gcongr
  have hWlower : 16 * t * q * L ≤ W + 1 := by
    calc
      16 * t * q * L ≤ 32 * t * q * L := by
        have hnonneg : 0 ≤ t * q * L := Nat.zero_le _
        nlinarith
      _ ≤ 32 * t * q * L + 1 := Nat.le_add_right _ _
  have hWlowerR : (16 : ℝ) * t * q * L ≤ (W : ℝ) + 1 := by
    exact_mod_cast hWlower
  have hprod : (2 : ℝ) * t * L ≤ r * ((W : ℝ) + 1) := by
    calc
      (2 : ℝ) * t * L = (1 / (8 * q)) * (16 * t * q * L) := by
        field_simp
        ring
      _ ≤ (1 / (8 * q)) * ((W : ℝ) + 1) := by
        gcongr
      _ ≤ r * ((W : ℝ) + 1) := by
        gcongr
  have hpowexp : (1 - r) ^ (W + 1) ≤ Real.exp (-r * ((W : ℝ) + 1)) := by
    calc
      (1 - r) ^ (W + 1) ≤ (Real.exp (-r)) ^ (W + 1) := by
        exact pow_le_pow_left₀ (sub_nonneg.mpr hrange.2)
          (Real.one_sub_le_exp_neg r) _
      _ = Real.exp (((W : ℝ) + 1) * (-r)) := by
        convert (Real.exp_nat_mul (-r) (W + 1)).symm using 1 <;> norm_num
      _ = Real.exp (-r * ((W : ℝ) + 1)) := by
        congr 1
        ring
  have hsmall_exp : Real.exp (-r * ((W : ℝ) + 1)) ≤
      Real.exp (-2 * (t : ℝ) * L) := by
    apply Real.exp_le_exp.mpr
    linarith [hprod]
  have hsmall_half : Real.exp (-((t : ℝ) * L)) < (1 / 2 : ℝ) := by
    have he := Real.exp_lt_exp.mpr (show -((t : ℝ) * L) < -Real.log 2 by linarith [htl])
    have he2 : Real.exp (-Real.log (2 : ℝ)) = (1 / 2 : ℝ) := by
      rw [Real.exp_neg, Real.exp_log (by norm_num)]
      norm_num
    rw [he2] at he
    exact he
  have hsmall_final : (2 : ℝ) * Real.exp (-((t : ℝ) * L)) < 1 := by
    nlinarith [hsmall_half]
  have hsmall : (n : ℝ) * (1 - r) ^ (W + 1) < 1 := by
    calc
      (n : ℝ) * (1 - r) ^ (W + 1) ≤
          (n : ℝ) * Real.exp (-r * ((W : ℝ) + 1)) := by
        exact mul_le_mul_of_nonneg_left hpowexp (by positivity)
      _ ≤ (n : ℝ) * Real.exp (-2 * (t : ℝ) * L) := by
        exact mul_le_mul_of_nonneg_left hsmall_exp (by positivity)
      _ ≤ 2 * (q : ℝ) ^ t * Real.exp (-2 * (t : ℝ) * L) := by
        exact mul_le_mul_of_nonneg_right hnhigh (by positivity)
      _ ≤ 2 * Real.exp ((t : ℝ) * L) * Real.exp (-2 * (t : ℝ) * L) := by
        exact mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hqt_exp (by norm_num)) (by positivity)
      _ = 2 * Real.exp (-((t : ℝ) * L)) := by
        calc
          2 * Real.exp ((t : ℝ) * L) * Real.exp (-2 * (t : ℝ) * L) =
              2 * (Real.exp ((t : ℝ) * L) * Real.exp (-2 * (t : ℝ) * L)) := by ring
          _ = 2 * Real.exp ((t : ℝ) * L + (-2 * (t : ℝ) * L)) := by
            rw [Real.exp_add]
          _ = 2 * Real.exp (-((t : ℝ) * L)) := by
            congr 1
            ring
      _ < 1 := hsmall_final
  have weight_le_length : ∀ (m : Nat) (z : Fin m → Bool), weight z ≤ m := by
    intro m
    induction m with
    | zero =>
        intro z
        simp [weight]
    | succ m ih =>
        intro z
        simp only [weight, Fin.sum_univ_castSucc]
        by_cases hz : z (Fin.last m) = true
        · have hcard : (Finset.univ.filter (fun i : Fin m =>
              z i.castSucc = true)).card ≤ m := by
            simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin m))
              (fun i => z i.castSucc = true))
          simpa [hz] using Nat.add_le_add_right hcard 1
        · have hcard : (Finset.univ.filter (fun i : Fin m =>
              z i.castSucc = true)).card ≤ m := by
            simpa using (Finset.card_filter_le (Finset.univ : Finset (Fin m))
              (fun i => z i.castSucc = true))
          simpa [hz] using Nat.le_succ_of_le hcard
  have support : ∀ (f : Fin k → D.vertex), valid k f → weight (sig f) ≤ W := by
    intro f hf
    by_contra hnot
    have hwu : W + 1 ≤ weight (sig f) := by omega
    have hkpos : 0 < k := lt_of_lt_of_le (by
      have htposN : 0 < t := by omega
      have hqposN : 0 < q := by omega
      have hLposN : 0 < L := hLpos
      dsimp [W]
      positivity) hWk
    let j : Fin k := ⟨k - 1, by omega⟩
    have hbmem : (f j).1.2 ∈ Bset f := by
      simp only [Bset, Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      by_cases hij : i = j
      · subst i
        exact (f j).2
      · have hijv : i.val ≠ k - 1 := by
          intro hv
          apply hij
          apply Fin.ext
          exact hv
        have hlt : i.val < j.val := by
          dsimp [j]
          omega
        have hno := hf hlt
        simpa [D, OldPairDigraph] using hno
    have hBpos : (1 : ℝ) ≤ (Bset f).card := by
      have hcardpos : 0 < (Bset f).card := Finset.card_pos.mpr ⟨_, hbmem⟩
      exact_mod_cast (Nat.succ_le_iff.mpr hcardpos)
    have hdec := decay k f hf
    obtain ⟨v, hv⟩ := Nat.exists_eq_add_of_le hwu
    have hpow : (1 - r) ^ weight (sig f) ≤ (1 - r) ^ (W + 1) := by
      rw [hv, pow_add]
      have hvpow : (1 - r) ^ v ≤ 1 :=
        pow_le_one₀ (sub_nonneg.mpr hrange.2) (sub_le_self 1 hrange.1)
      have hnon : 0 ≤ (1 - r) ^ (W + 1) :=
        pow_nonneg (sub_nonneg.mpr hrange.2) _
      simpa using mul_le_mul_of_nonneg_left hvpow hnon
    have hbound : (Bset f).card ≤ (n : ℝ) * (1 - r) ^ (W + 1) :=
      hdec.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
    nlinarith [hBpos, hbound, hsmall]
  let Fiber : ∀ m : Nat, (Fin m → Bool) → Type := fun m z =>
    {p : Path m // ∀ i, sig p.1 i = z i}
  let PrefixFiber : ∀ m : Nat, (Fin (m + 1) → Bool) → Type := fun m z =>
    {p : Path m // ∀ i, sig p.1 i = z i.castSucc}
  let ChildFiber : ∀ (m : Nat) (z : Fin (m + 1) → Bool), PrefixFiber m z → Type :=
    fun m z p =>
      {x : Ext m p.1 // sig (Fin.snoc p.1 x.1) (Fin.last m) = z (Fin.last m)}
  let count : (Fin k → Bool) → Nat := fun z => Fintype.card (Fiber k z)
  have fiber_succ_equiv (m : Nat) (z : Fin (m + 1) → Bool) :
      Fiber (m + 1) z ≃ Σ p : PrefixFiber m z, ChildFiber m z p := by
    let toFun : Fiber (m + 1) z → Σ p : PrefixFiber m z, ChildFiber m z p :=
      fun y =>
        ⟨⟨⟨Fin.init y.1.1, by
            intro i j hij
            exact y.1.2 (i := i.castSucc) (j := j.castSucc) (by simpa using hij)⟩,
          by
            intro i
            calc
              sig (Fin.init y.1.1) i =
                  sig (Fin.snoc (Fin.init y.1.1) (y.1.1 (Fin.last m))) i.castSucc :=
                    (sig_snoc_castSucc _ _ _).symm
              _ = sig y.1.1 i.castSucc := by rw [Fin.snoc_init_self]
              _ = z i.castSucc := y.2 _⟩,
          ⟨⟨y.1.1 (Fin.last m), by
              rw [Fin.snoc_init_self]
              exact y.1.2⟩,
            by
              rw [Fin.snoc_init_self]
              exact y.2 _⟩⟩
    let invFun : (Σ p : PrefixFiber m z, ChildFiber m z p) → Fiber (m + 1) z :=
      fun y =>
        ⟨⟨Fin.snoc y.1.1 y.2.1, y.2.1.2⟩, by
          intro i
          refine Fin.lastCases ?_ (fun i => ?_) i
          · exact y.2.2
          · calc
              sig (Fin.snoc y.1.1 y.2.1) i.castSucc = sig y.1.1 i :=
                sig_snoc_castSucc _ _ _
              _ = z i.castSucc := y.1.2 i⟩
    have left_inv (y : Fiber (m + 1) z) : invFun (toFun y) = y := by
      apply Subtype.ext
      apply Subtype.ext
      dsimp [invFun, toFun]
      exact Fin.snoc_init_self y.1.1
    have right_inv (y : Σ p : PrefixFiber m z, ChildFiber m z p) :
        toFun (invFun y) = y := by
      rcases y with ⟨p, x⟩
      have hp : (toFun (invFun (⟨p, x⟩))).1 = p := by
        apply Subtype.ext
        apply Subtype.ext
        dsimp [toFun, invFun]
        change Fin.init (Fin.snoc (α := fun _ : Fin (m + 1) => D.vertex)
          p.1.1 x.1.1) = p.1.1
        exact Fin.init_snoc (α := fun _ : Fin (m + 1) => D.vertex) x.1.1 p.1.1
      apply Sigma.ext_iff.mpr
      refine ⟨hp, ?_⟩
      have cast_child_val {p q : PrefixFiber m z} (h : p = q)
          (a : ChildFiber m z p) :
          ((cast (congrArg (fun u : PrefixFiber m z => ChildFiber m z u) h) a :
            ChildFiber m z q).1.1 : D.vertex) = a.1.1 := by
        cases h
        rfl
      exact heq_of_cast_eq
        (congrArg (fun u : PrefixFiber m z => ChildFiber m z u) hp) (by
          apply Subtype.ext
          apply Subtype.ext
          calc
            ((cast (congrArg (fun u : PrefixFiber m z => ChildFiber m z u) hp)
                (toFun (invFun (⟨p, x⟩))).2 : ChildFiber m z p).1.1 : D.vertex) =
                ((toFun (invFun (⟨p, x⟩))).2.1.1 : D.vertex) := cast_child_val hp _
            _ = x.1.1 := by
              change (Fin.snoc (α := fun _ : Fin (m + 1) => D.vertex) p.1 x.1.1)
                (Fin.last m) = x.1.1
              exact Fin.snoc_last _ _)
    exact Equiv.mk toFun invFun left_inv right_inv
  let Delta : Nat := n ^ 2
  have hExtcard : ∀ (m : Nat) (p : Path m), Fintype.card (Ext m p) ≤ Delta := by
    intro m p
    let e : Ext m p → D.vertex := fun x => x.1
    have he : Function.Injective e := by
      intro x y hxy
      exact Subtype.ext hxy
    have hc := Fintype.card_le_of_injective e he
    exact hc.trans (by simpa [Delta] using hDcard)
  have hchild : ∀ (m : Nat) (z : Fin (m + 1) → Bool)
      (p : PrefixFiber m z),
      Fintype.card (ChildFiber m z p) ≤
        (if z (Fin.last m) = true then Delta else h) := by
    intro m z p
    by_cases hz : z (Fin.last m) = true
    · rw [if_pos hz]
      let e : ChildFiber m z p → Ext m p.1 := fun x => x.1
      have he : Function.Injective e := by
        intro x y hxy
        exact Subtype.ext hxy
      exact (Fintype.card_le_of_injective e he).trans (hExtcard m p.1)
    · rw [if_neg hz]
      let e : ChildFiber m z p →
          {x : D.vertex // ¬unmarked p.1.1 x ∧
            valid (m + 1) (Fin.snoc p.1.1 x)} := fun y => by
        have hm : ¬unmarked p.1.1 y.1.1 := by
          intro hu
          have hs := y.2
          rw [sig_snoc_last] at hs
          have hs' : z (Fin.last m) = true := by simpa [hu] using hs
          exact hz hs'
        exact ⟨y.1.1, hm, y.1.2⟩
      have he : Function.Injective e := by
        intro x y hxy
        apply Subtype.ext
        apply Subtype.ext
        exact congrArg (fun u => u.1) hxy
      have hc := Fintype.card_le_of_injective e he
      exact hc.trans (by simpa using hmarked p.1.1)
  have hweight_snoc (m : Nat) (z : Fin (m + 1) → Bool) :
      weight z = weight (fun i : Fin m => z i.castSucc) +
        if z (Fin.last m) = true then 1 else 0 := by
    simp only [weight, Fin.sum_univ_castSucc]
  have hcount : ∀ (m : Nat) (z : Fin m → Bool),
      Fintype.card (Fiber m z) ≤ Delta ^ weight z * h ^ (m - weight z) := by
    intro m
    induction m with
    | zero =>
        intro z
        let e : Fiber 0 z → Unit := fun _ => ()
        have he : Function.Injective e := by
          intro a b
          intro _
          apply Subtype.ext
          apply Subtype.ext
          funext i
          exact Fin.elim0 i
        have hc := Fintype.card_le_of_injective e he
        simpa [Fiber, weight, Delta] using hc
    | succ m ih =>
        intro z
        let zpre : Fin m → Bool := fun i => z i.castSucc
        have hwz : weight z = weight zpre +
            if z (Fin.last m) = true then 1 else 0 := by
          simpa [zpre] using hweight_snoc m z
        have hcard_sigma : Fintype.card (Fiber (m + 1) z) =
            ∑ p : PrefixFiber m z, Fintype.card (ChildFiber m z p) := by
          calc
            Fintype.card (Fiber (m + 1) z) =
                Fintype.card (Σ p : PrefixFiber m z, ChildFiber m z p) :=
              Fintype.card_congr (fiber_succ_equiv m z)
            _ = ∑ p : PrefixFiber m z, Fintype.card (ChildFiber m z p) :=
              Fintype.card_sigma
        have hsum : (∑ p : PrefixFiber m z, Fintype.card (ChildFiber m z p)) ≤
            Fintype.card (PrefixFiber m z) *
              (if z (Fin.last m) = true then Delta else h) := by
          calc
            (∑ p : PrefixFiber m z, Fintype.card (ChildFiber m z p)) ≤
                ∑ p : PrefixFiber m z, (if z (Fin.last m) = true then Delta else h) :=
              Finset.sum_le_sum (fun p _ => hchild m z p)
            _ = Fintype.card (PrefixFiber m z) *
                (if z (Fin.last m) = true then Delta else h) := by
              simp
        have hbase : Fintype.card (PrefixFiber m z) ≤
            Delta ^ weight zpre * h ^ (m - weight zpre) := by
          simpa [PrefixFiber, Fiber, zpre] using ih zpre
        have hmain : Fintype.card (Fiber (m + 1) z) ≤
            (Delta ^ weight zpre * h ^ (m - weight zpre)) *
              (if z (Fin.last m) = true then Delta else h) := by
          rw [hcard_sigma]
          exact hsum.trans (Nat.mul_le_mul_right _ hbase)
        have hwle := weight_le_length m zpre
        have hsub_true : m + 1 - (weight zpre + 1) = m - weight zpre := by
          omega
        have hsub_false : m + 1 - weight zpre = (m - weight zpre) + 1 := by
          omega
        by_cases hz : z (Fin.last m) = true
        · calc
            Fintype.card (Fiber (m + 1) z) ≤
                (Delta ^ weight zpre * h ^ (m - weight zpre)) * Delta := by
                  simpa [hz] using hmain
            _ = Delta ^ (weight zpre + 1) * h ^ (m - weight zpre) := by
                  rw [pow_succ]
                  ring
            _ = Delta ^ weight z * h ^ ((m + 1) - weight z) := by
                  rw [hwz, if_pos hz]
                  rw [hsub_true]
        ·
          calc
            Fintype.card (Fiber (m + 1) z) ≤
                (Delta ^ weight zpre * h ^ (m - weight zpre)) * h := by
                  simpa [hz] using hmain
            _ = Delta ^ weight zpre * h ^ ((m - weight zpre) + 1) := by
                  calc
                    Delta ^ weight zpre * h ^ (m - weight zpre) * h =
                        Delta ^ weight zpre * (h ^ (m - weight zpre) * h) := by ring
                    _ = Delta ^ weight zpre * h ^ ((m - weight zpre) + 1) := by
                      rw [← pow_succ]
            _ = Delta ^ weight z * h ^ ((m + 1) - weight z) := by
                  rw [hwz, if_neg hz]
                  simp only [Nat.add_zero]
                  rw [hsub_false]
  have hd16 : 16 ≤ d := by
    rw [hdform]
    apply (Nat.le_div_iff_mul_le (by omega : 0 < q - 1)).2
    have hpow2 : q ^ 2 ≤ q ^ t :=
      Nat.pow_le_pow_right (by omega : 0 < q) (by omega : 2 ≤ t)
    calc
      16 * (q - 1) ≤ q * (q - 1) := Nat.mul_le_mul_right _ hq
      _ = q * q - q := by simpa using Nat.mul_sub_left_distrib q q 1
      _ = q ^ 2 - q := by rw [pow_two]
      _ ≤ q ^ 2 - 1 := Nat.sub_le_sub_left (by omega : 1 ≤ q) _
      _ ≤ q ^ t - 1 := Nat.sub_le_sub_right hpow2 1
  have hlamnonneg : 0 ≤ lambda := by
    rw [hlam]
    exact Real.sqrt_nonneg _
  have hsqrt : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
  have hsqrt_sq : (Real.sqrt (d : ℝ)) ^ 2 = (d : ℝ) := by
    rw [Real.sq_sqrt]
    positivity
  have hlam_sq : lambda ^ 2 ≤ 4 * (d : ℝ) := by
    nlinarith [hlamhigh]
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  have hd16R : (16 : ℝ) ≤ d := by exact_mod_cast hd16
  have hfrac : 4 * lambda ^ 2 / (d : ℝ) ^ 2 ≤ 1 := by
    apply (div_le_iff₀ (sq_pos_of_pos hdR)).2
    nlinarith [hlam_sq]
  have hHle : H ≤ (n : ℝ) ^ 2 := by
    dsimp [H]
    simpa using mul_le_mul_of_nonneg_right hfrac (sq_nonneg _)
  have hfloor : (h : ℝ) ≤ H := by
    exact Nat.floor_le (by positivity)
  have hh : h ≤ Delta := by
    have hhR : (h : ℝ) ≤ (n : ℝ) ^ 2 := hfloor.trans hHle
    exact_mod_cast hhR
  have hsupport : ∀ z, count z > 0 → weight z ≤ W := by
    intro z hz
    have hz' : 0 < Fintype.card (Fiber k z) := by simpa [count] using hz
    rcases Fintype.card_pos_iff.mp hz' with ⟨y⟩
    have hs : sig y.1.1 = z := funext y.2
    rw [← hs]
    exact support y.1.1 y.1.2
  let sigToFiber : Path k → Σ z : Fin k → Bool, Fiber k z := fun p =>
    ⟨sig p.1, ⟨p, by intro i; rfl⟩⟩
  let fiberToSig : (Σ z : Fin k → Bool, Fiber k z) → Path k := fun y => y.2.1
  have sig_fiber_equiv : Path k ≃ Σ z : Fin k → Bool, Fiber k z := by
    have left_inv : Function.LeftInverse fiberToSig sigToFiber := by
      intro p
      rfl
    have right_inv : Function.RightInverse fiberToSig sigToFiber := by
      intro y
      rcases y with ⟨z, p⟩
      have hz : sig p.1 = z := funext p.2
      apply Sigma.ext_iff.mpr
      refine ⟨hz, ?_⟩
      have cast_fiber_val {z₁ z₂ : Fin k → Bool} (e : z₁ = z₂)
          (a : Fiber k z₁) :
          ((cast (congrArg (fun u : Fin k → Bool => Fiber k u) e) a :
            Fiber k z₂).1 : Path k) = a.1 := by
        cases e
        rfl
      exact heq_of_cast_eq
        (congrArg (fun u : Fin k → Bool => Fiber k u) hz) (by
          apply Subtype.ext
          exact cast_fiber_val hz _)
    exact Equiv.mk sigToFiber fiberToSig left_inv right_inv
  have hpath_sigma : Fintype.card (Path k) = ∑ z, count z := by
    calc
      Fintype.card (Path k) =
          Fintype.card (Σ z : Fin k → Bool, Fiber k z) :=
        Fintype.card_congr sig_fiber_equiv
      _ = ∑ z, Fintype.card (Fiber k z) := Fintype.card_sigma
      _ = ∑ z, count z := by rfl
  have hpath_count : Fintype.card (Path k) =
      ForwardIndependentCount (OldPairDigraph G) k := by
    unfold ForwardIndependentCount
    dsimp [Path, valid, D]
  have hcount' : ∀ z, count z ≤ Delta ^
      (∑ i, (if z i = true then 1 else 0)) *
        h ^ (k - ∑ i, (if z i = true then 1 else 0)) := by
    intro z
    simpa [weight] using hcount k z
  have hsupport' : ∀ z, count z > 0 →
      (∑ i, (if z i = true then 1 else 0)) ≤ W := by
    intro z hz
    simpa [weight] using hsupport z hz
  have htree : (∑ z, count z) ≤
      2 ^ k * Delta ^ W * h ^ (k - W) := by
    exact RootedTreeCounting k W Delta h count
      hcount' hsupport' hh hWk
  have hnat : ForwardIndependentCount (OldPairDigraph G) k ≤
      2 ^ k * Delta ^ W * h ^ (k - W) := by
    calc
      ForwardIndependentCount (OldPairDigraph G) k = Fintype.card (Path k) :=
        hpath_count.symm
      _ = ∑ z, count z := hpath_sigma
      _ ≤ 2 ^ k * Delta ^ W * h ^ (k - W) := htree
  have hreal : (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
      ((2 ^ k * Delta ^ W * h ^ (k - W) : Nat) : ℝ) := by
    exact_mod_cast hnat
  have hmainreal : (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
      (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * H ^ (k - W) := by
    calc
      (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
          ((2 ^ k * Delta ^ W * h ^ (k - W) : Nat) : ℝ) := hreal
      _ = (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * (h : ℝ) ^ (k - W) := by
        norm_num [Delta, Nat.cast_mul, Nat.cast_pow, ← pow_mul]
      _ ≤ (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * H ^ (k - W) := by
        gcongr
  have hident : (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * H ^ (k - W) =
      (2 : ℝ) ^ k * 4 ^ (k - W) *
        (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) * (n : ℝ) ^ (2 * k) := by
    rw [show H = 4 * (lambda ^ 2 / (d : ℝ) ^ 2) * (n : ℝ) ^ 2 by
      dsimp [H]
      ring]
    rw [mul_pow, mul_pow]
    rw [← pow_mul (n : ℝ) 2 (k - W)]
    calc
      (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) *
          (4 ^ (k - W) * (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
            (n : ℝ) ^ (2 * (k - W))) =
          (2 : ℝ) ^ k * 4 ^ (k - W) *
            (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
            ((n : ℝ) ^ (2 * W) * (n : ℝ) ^ (2 * (k - W))) := by ring
      _ = (2 : ℝ) ^ k * 4 ^ (k - W) *
            (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
            (n : ℝ) ^ (2 * W + 2 * (k - W)) := by
              rw [← pow_add]
      _ = (2 : ℝ) ^ k * 4 ^ (k - W) *
            (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
            (n : ℝ) ^ (2 * k) := by
              have hmul : 2 * (k - W) = 2 * k - 2 * W := by
                rw [Nat.mul_sub_left_distrib]
              have hexp : 2 * W + 2 * (k - W) = 2 * k := by
                rw [hmul]
                omega
              rw [hexp]
  have hcoeff : (2 : ℝ) ^ k * 4 ^ (k - W) ≤ 8 ^ k := by
    calc
      (2 : ℝ) ^ k * 4 ^ (k - W) ≤ (2 : ℝ) ^ k * 4 ^ k := by
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)) (by positivity)
      _ = 8 ^ k := by
        rw [show (8 : ℝ) = 2 * 4 by norm_num, mul_pow]
  have hfinal : (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * H ^ (k - W) ≤
      8 ^ k * (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) * (n : ℝ) ^ (2 * k) := by
    rw [hident]
    calc
      (2 : ℝ) ^ k * 4 ^ (k - W) *
          (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) * (n : ℝ) ^ (2 * k) =
          ((2 : ℝ) ^ k * 4 ^ (k - W)) *
            ((lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) * (n : ℝ) ^ (2 * k)) := by ring
      _ ≤ 8 ^ k *
            ((lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) * (n : ℝ) ^ (2 * k)) := by
        exact mul_le_mul_of_nonneg_right hcoeff (by positivity)
      _ = 8 ^ k * (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
            (n : ℝ) ^ (2 * k) := by ring
  calc
    (ForwardIndependentCount (OldPairDigraph G) k : ℝ) ≤
        (2 : ℝ) ^ k * (n : ℝ) ^ (2 * W) * H ^ (k - W) := hmainreal
    _ ≤ 8 ^ k * (lambda ^ 2 / (d : ℝ) ^ 2) ^ (k - W) *
        (n : ℝ) ^ (2 * k) := hfinal
    _ = (8 : ℝ) ^ k * (lambda ^ 2 / d ^ 2) ^
          (k - 32 * t * q * Nat.ceil (Real.log (q : ℝ))) *
        (n : ℝ) ^ (2 * k) := by rfl
