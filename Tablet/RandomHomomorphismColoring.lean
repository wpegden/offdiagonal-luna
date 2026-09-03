import Tablet.CompleteColoring
import Tablet.ForwardIndependentCount
import Tablet.MonochromaticClique
import Tablet.TransitiveTournament
import Mathlib.Data.Fintype.Sort

-- [TABLET NODE: RandomHomomorphismColoring]
theorem RandomHomomorphismColoring
    (D : LooplessDigraph) (s ell n : Nat)
    (hs : 0 < s) (hell : 0 < ell)
    (horder : 0 < @Fintype.card D.vertex D.fintype)
    (hfree : ¬ Nonempty (TransitiveTournament D s))
    (hprob : (Nat.choose n s : ℝ) *
        ((ForwardIndependentCount D s : ℝ) /
          (@Fintype.card D.vertex D.fintype : ℝ) ^ s) ^ (ell - 1) < 1) :
    ∃ c : CompleteColoring n ell,
      ¬ Nonempty (MonochromaticClique c s) := by
-- BODY
  classical
  letI := D.fintype
  let N : Nat := @Fintype.card D.vertex D.fintype
  let L : Nat := ell - 1
  let Ω := Fin L → Fin n → D.vertex
  let fp : (Fin s → D.vertex) → Prop := fun f =>
    ∀ ⦃i j : Fin s⦄, i.val < j.val → ¬ D.arc (f i) (f j)
  let F : Nat := ForwardIndependentCount D s
  have hL : 1 ≤ ell := hell
  have hLadd : L + 1 = ell := by
    dsimp [L]
    omega
  have hN : 0 < N := by
    exact horder
  let emb : Fin L → Fin ell := fun i =>
    ⟨i.val, lt_of_lt_of_le i.isLt (Nat.sub_le _ _)⟩
  let last : Fin ell := ⟨L, by dsimp [L]; omega⟩
  let edgeColor (ω : Ω) (u v : Fin n) : Fin ell :=
    if h : ∃ c : Fin L, D.arc (ω c u) (ω c v) then
      emb (Fin.find (fun c : Fin L => D.arc (ω c u) (ω c v)) h)
    else last
  let coloring (ω : Ω) : CompleteColoring n ell :=
    { color := fun u v =>
        if u.val < v.val then edgeColor ω u v else edgeColor ω v u
      symmetric := by
        intro u v
        by_cases huv : u.val < v.val
        · have hvu : ¬v.val < u.val := not_lt_of_ge (Nat.le_of_lt huv)
          simp [huv, hvu]
        · by_cases heq : u = v
          · subst heq
            rfl
          · have hvu : v.val < u.val := by omega
            simp [huv, hvu] }
  have hedge_lower : ∀ (ω : Ω) (u v : Fin n) (c : Fin ell),
      ∀ hc : c.val < L, edgeColor ω u v = c →
        D.arc (ω ⟨c.val, hc⟩ u) (ω ⟨c.val, hc⟩ v) := by
    intro ω u v c hc heq
    dsimp [edgeColor] at heq
    split_ifs at heq with hex
    · have hfind : Fin.find (fun d : Fin L => D.arc (ω d u) (ω d v)) hex =
          ⟨c.val, hc⟩ := by
        apply Fin.ext
        simpa [emb] using congrArg Fin.val heq
      simpa [hfind] using Fin.find_spec hex
    · have : L = c.val := by
        simpa [last] using congrArg Fin.val heq
      omega
  have hedge_final : ∀ (ω : Ω) (u v : Fin n),
      edgeColor ω u v = last → ∀ d : Fin L,
        ¬D.arc (ω d u) (ω d v) := by
    intro ω u v heq d hd
    dsimp [edgeColor] at heq
    split_ifs at heq with hex
    · have hval := congrArg Fin.val heq
      have hfindlt :=
        (Fin.find (fun c : Fin L => D.arc (ω c u) (ω c v)) hex).isLt
      dsimp [emb, last] at hval
      omega
    · exact hex ⟨d, hd⟩
  let Sets := {S : Finset (Fin n) // S.card = s}
  let compCard (S : Sets) : (S.1ᶜ : Finset (Fin n)).card = n - s := by
    dsimp [Sets] at S
    simpa [S.2] using (Finset.card_compl S.1)
  let event (S : Sets) (ω : Ω) : Prop :=
    ∀ c : Fin L, ∀ ⦃i j : Fin s⦄, i.val < j.val →
      ¬ D.arc (ω c (S.1.orderEmbOfFin S.2 i))
        (ω c (S.1.orderEmbOfFin S.2 j))
  let bad (ω : Ω) : Prop := ∃ S : Sets, event S ω
  have hgood_card : ∀ S : Sets,
      Fintype.card {ω : Ω // event S ω} ≤
        F ^ L * N ^ (L * (n - s)) := by
    intro S
    let eidx : Fin s ⊕ Fin (n - s) ≃ Fin n :=
      finSumEquivOfFinset S.2 (compCard S)
    let eone : (Fin n → D.vertex) ≃
        (Fin s → D.vertex) × (Fin (n - s) → D.vertex) :=
      (Equiv.piCongrLeft (fun _ : Fin n => D.vertex) eidx).symm.trans
        (Equiv.sumArrowEquivProdArrow (Fin s) (Fin (n - s)) D.vertex)
    let eω : Ω ≃
        (Fin L → Fin s → D.vertex) ×
          (Fin L → Fin (n - s) → D.vertex) :=
      (Equiv.piCongrRight (fun _ : Fin L => eone)).trans
        (Equiv.arrowProdEquivProdArrow (Fin L)
          (fun _ => Fin s → D.vertex) (fun _ => Fin (n - s) → D.vertex))
    let R := {r : Fin L → Fin s → D.vertex // ∀ c, fp (r c)}
    let E := {ω : Ω // event S ω}
    have hrestrict : ∀ (ω : Ω) (c : Fin L) (i : Fin s),
        (eω ω).1 c i = ω c (S.1.orderEmbOfFin S.2 i) := by
      intro ω c i
      dsimp [eω, eone]
      change ω c (eidx (Sum.inl i)) = _
      rw [finSumEquivOfFinset_inl]
    let mapE : E → R × (Fin L → Fin (n - s) → D.vertex) := fun ω =>
      ⟨⟨(eω ω.1).1, by
          intro c
          intro i j hij harc
          rw [hrestrict ω.1 c i, hrestrict ω.1 c j] at harc
          exact ω.2 c hij harc⟩, (eω ω.1).2⟩
    have hmapE : Function.Injective mapE := by
      intro ω₁ ω₂ hω
      apply Subtype.ext
      apply eω.injective
      apply Prod.ext
      · exact congrArg (fun z => z.1.1) hω
      · exact congrArg (fun z => z.2) hω
    have hcardR : Fintype.card R = F ^ L := by
      have he : R ≃ ∀ c : Fin L, {f : Fin s → D.vertex // fp f} :=
        Equiv.subtypePiEquivPi
      rw [Fintype.card_congr he]
      have hF : Fintype.card {f : Fin s → D.vertex // fp f} = F := by
        simp [F, ForwardIndependentCount, fp]
      simp [Fintype.card_pi_const, hF]
    have hcardO : Fintype.card (Fin L → Fin (n - s) → D.vertex) =
        N ^ (L * (n - s)) := by
      simp only [Fintype.card_fun, Fintype.card_fin]
      calc
        (N ^ (n - s)) ^ L = N ^ ((n - s) * L) :=
          (pow_mul N (n - s) L).symm
        _ = N ^ (L * (n - s)) := by rw [Nat.mul_comm]
    have hcardmap : Fintype.card E ≤
        Fintype.card R * Fintype.card (Fin L → Fin (n - s) → D.vertex) := by
      simpa [Fintype.card_prod] using Fintype.card_le_of_injective mapE hmapE
    dsimp [E] at hcardmap
    rw [hcardR, hcardO] at hcardmap
    exact hcardmap
  have hcard_sets : Fintype.card Sets = Nat.choose n s := by
    dsimp [Sets]
    simp
  have hbad_nat : Fintype.card {ω : Ω // bad ω} ≤
      Nat.choose n s * (F ^ L * N ^ (L * (n - s))) := by
    let B := {ω : Ω // bad ω}
    let SigmaE := Sigma fun S : Sets => {ω : Ω // event S ω}
    let pick : B → SigmaE := fun ω =>
      ⟨Classical.choose ω.2, ⟨ω.1, Classical.choose_spec ω.2⟩⟩
    have hpick : Function.Injective pick := by
      intro ω₁ ω₂ hω
      apply Subtype.ext
      have hS : Classical.choose ω₁.2 = Classical.choose ω₂.2 :=
        congrArg Sigma.fst hω
      have hv : (ω₁.1 : Ω) = ω₂.1 := by
        have := congrArg (fun z : SigmaE => (z.2 : Ω)) hω
        simpa [pick, hS] using this
      exact hv
    have hcardpick : Fintype.card B ≤ Fintype.card SigmaE :=
      Fintype.card_le_of_injective pick hpick
    calc
      Fintype.card B ≤ Fintype.card SigmaE := hcardpick
      _ = ∑ S : Sets, Fintype.card {ω : Ω // event S ω} := by
        rw [Fintype.card_sigma]
      _ ≤ ∑ _S : Sets, (F ^ L * N ^ (L * (n - s))) := by
        apply Finset.sum_le_sum
        intro S hS
        exact hgood_card S
      _ = Nat.choose n s * (F ^ L * N ^ (L * (n - s))) := by
        simp [hcard_sets]
  have hstrict : Nat.choose n s * (F ^ L * N ^ (L * (n - s))) <
      N ^ (L * n) := by
    by_cases hsn : s ≤ n
    · have hpow : ((N : ℝ) ^ s) ^ L * (N : ℝ) ^ (L * (n - s)) =
          (N : ℝ) ^ (L * n) := by
        have hexp : (s * L + L * (n - s) : Nat) = L * n := by
          calc
            s * L + L * (n - s) = L * s + (L * n - L * s) := by
              rw [Nat.mul_sub_left_distrib L n s, Nat.mul_comm s L]
            _ = L * n := Nat.add_sub_of_le (Nat.mul_le_mul_left L hsn)
        rw [← pow_mul, ← pow_add, hexp]
      have hpospow : (0 : ℝ) < (N : ℝ) ^ (L * n) := by positivity
      have hmain : (Nat.choose n s : ℝ) * (F : ℝ) ^ L *
          (N : ℝ) ^ (L * (n - s)) < (N : ℝ) ^ (L * n) := by
        calc
          (Nat.choose n s : ℝ) * (F : ℝ) ^ L *
              (N : ℝ) ^ (L * (n - s)) =
              (Nat.choose n s : ℝ) *
                ((F : ℝ) / (N : ℝ) ^ s) ^ L *
                (N : ℝ) ^ (L * n) := by
                  rw [div_pow]
                  field_simp [show (N : ℝ) ≠ 0 by
                    exact_mod_cast (Nat.ne_of_gt hN)]
                  rw [← hpow]
                  field_simp [show (N : ℝ) ≠ 0 by
                    exact_mod_cast (Nat.ne_of_gt hN)]
          _ < (1 : ℝ) * (N : ℝ) ^ (L * n) :=
            mul_lt_mul_of_pos_right hprob hpospow
          _ = (N : ℝ) ^ (L * n) := one_mul _
      have hmain' :
          ((Nat.choose n s * (F ^ L * N ^ (L * (n - s))) : Nat) : ℝ) <
            ((N ^ (L * n) : Nat) : ℝ) := by
        norm_num [Nat.cast_mul, Nat.cast_pow]
        simpa [mul_assoc] using hmain
      exact_mod_cast hmain'
    · have hz : Nat.choose n s = 0 := Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hsn)
      simp [hz]
      positivity
  have hΩcard : Fintype.card Ω = N ^ (L * n) := by
    simp only [Ω, Fintype.card_fun, Fintype.card_fin]
    calc
      (N ^ n) ^ L = N ^ (n * L) := (pow_mul N n L).symm
      _ = N ^ (L * n) := by rw [Nat.mul_comm]
  have hnotbad : ∃ ω : Ω, ¬bad ω := by
    have hlt : Fintype.card {ω : Ω // bad ω} < Fintype.card Ω := by
      rw [hΩcard]
      exact hbad_nat.trans_lt hstrict
    have hpos : 0 < Fintype.card {ω : Ω // ¬bad ω} := by
      rw [Fintype.card_subtype_compl]
      exact Nat.sub_pos_of_lt hlt
    rcases Fintype.card_pos_iff.mp hpos with ⟨ω⟩
    exact ⟨ω.1, ω.2⟩
  rcases hnotbad with ⟨ω, hω⟩
  have hlow : ¬Nonempty (MonochromaticClique (coloring ω) s) := by
    intro hc
    rcases hc with ⟨mc⟩
    rcases mc.monochromatic with ⟨col, hcol⟩
    by_cases hcolLt : col.val < L
    · have hS : (Finset.univ.image mc.vertex).card = s := by
        rw [Finset.card_image_of_injective _ mc.injective]
        simp [hs]
      let S : Sets := ⟨Finset.univ.image mc.vertex, hS⟩
      let y : Fin s → D.vertex := fun i =>
        ω ⟨col.val, hcolLt⟩ (S.1.orderEmbOfFin S.2 i)
      have hyarc : ∀ ⦃i j : Fin s⦄, i.val < j.val →
          D.arc (y i) (y j) := by
        intro i j hij
        have hi : S.1.orderEmbOfFin S.2 i ∈ S.1 :=
          Finset.orderEmbOfFin_mem _ _ _
        have hj : S.1.orderEmbOfFin S.2 j ∈ S.1 :=
          Finset.orderEmbOfFin_mem _ _ _
        rcases Finset.mem_image.mp hi with ⟨ii, _, hii⟩
        rcases Finset.mem_image.mp hj with ⟨jj, _, hjj⟩
        have hltxy : (S.1.orderEmbOfFin S.2 i).val <
            (S.1.orderEmbOfFin S.2 j).val :=
          (S.1.orderEmbOfFin S.2).strictMono hij
        have hne : ii ≠ jj := by
          intro heq
          have heq' : (S.1.orderEmbOfFin S.2 i).val =
              (S.1.orderEmbOfFin S.2 j).val := by
            calc
              (S.1.orderEmbOfFin S.2 i).val = (mc.vertex ii).val :=
                congrArg Fin.val hii.symm
              _ = (mc.vertex jj).val := by rw [heq]
              _ = (S.1.orderEmbOfFin S.2 j).val := congrArg Fin.val hjj
          exact (ne_of_lt hltxy) heq'
        have hce := hcol hne
        have he : edgeColor ω (S.1.orderEmbOfFin S.2 i)
            (S.1.orderEmbOfFin S.2 j) = col := by
          simpa [coloring, hltxy, hii, hjj] using hce
        simpa [y] using hedge_lower ω _ _ col hcolLt he
      have hyinj : Function.Injective y := by
        intro i j heq
        by_contra hne
        rcases lt_or_gt_of_ne hne with hij | hji
        · have ha := hyarc hij
          exact (D.loopless (y j)) (by rw [heq] at ha; exact ha)
        · have ha := hyarc hji
          exact (D.loopless (y i)) (by rw [← heq] at ha; exact ha)
      exact hfree ⟨{ vertex := y, injective := hyinj, forwardArc := hyarc }⟩
    · have hcolLast : col = last := by
        apply Fin.ext
        dsimp [last]
        omega
      have hS : (Finset.univ.image mc.vertex).card = s := by
        rw [Finset.card_image_of_injective _ mc.injective]
        simp [hs]
      let S : Sets := ⟨Finset.univ.image mc.vertex, hS⟩
      have hevent : event S ω := by
        intro d i j hij
        intro harc
        have hi : S.1.orderEmbOfFin S.2 i ∈ S.1 :=
          Finset.orderEmbOfFin_mem _ _ _
        have hj : S.1.orderEmbOfFin S.2 j ∈ S.1 :=
          Finset.orderEmbOfFin_mem _ _ _
        rcases Finset.mem_image.mp hi with ⟨ii, _, hii⟩
        rcases Finset.mem_image.mp hj with ⟨jj, _, hjj⟩
        have hltxy : (S.1.orderEmbOfFin S.2 i).val <
            (S.1.orderEmbOfFin S.2 j).val :=
          (S.1.orderEmbOfFin S.2).strictMono hij
        have hne : ii ≠ jj := by
          intro heq
          have heq' : (S.1.orderEmbOfFin S.2 i).val =
              (S.1.orderEmbOfFin S.2 j).val := by
            calc
              (S.1.orderEmbOfFin S.2 i).val = (mc.vertex ii).val :=
                congrArg Fin.val hii.symm
              _ = (mc.vertex jj).val := by rw [heq]
              _ = (S.1.orderEmbOfFin S.2 j).val := congrArg Fin.val hjj
          exact (ne_of_lt hltxy) heq'
        have hce := hcol hne
        have he : edgeColor ω (S.1.orderEmbOfFin S.2 i)
            (S.1.orderEmbOfFin S.2 j) = col := by
          simpa [coloring, hltxy, hii, hjj] using hce
        exact hedge_final ω _ _ (hcolLast ▸ he) d harc
      exact hω ⟨S, hevent⟩
  exact ⟨coloring ω, hlow⟩
