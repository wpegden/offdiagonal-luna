import Tablet.CliqueWitness
import Tablet.ForwardIndependentCount
import Tablet.IndependentSetCount
import Tablet.TransitiveTournament
import Mathlib.Analysis.SpecialFunctions.Stirling

-- [TABLET NODE: RandomPermutationReduction]
theorem RandomPermutationReduction
    (D : LooplessDigraph) (s k : Nat)
    (hfree : ¬ Nonempty (TransitiveTournament D s)) (hk : 1 ≤ k) :
    ∃ G : LoopGraph,
      @Fintype.card G.vertex G.fintype = @Fintype.card D.vertex D.fintype ∧
      (∀ v, ¬ G.adj v v) ∧
      ¬ Nonempty (CliqueWitness G s) ∧
      (IndependentSetCount G k : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          (ForwardIndependentCount D k : ℝ) := by
-- BODY
  classical
  letI := D.fintype
  let n := Fintype.card D.vertex
  let e : D.vertex ≃ Fin n := Fintype.equivFin D.vertex
  let P := Equiv.Perm (Fin n)
  let ord (π : P) (v : D.vertex) : Fin n := π (e v)
  let adj (π : P) (u v : D.vertex) : Prop :=
    (ord π u < ord π v ∧ D.arc u v) ∨
      (ord π v < ord π u ∧ D.arc v u)
  let graph (π : P) : LoopGraph :=
    { vertex := D.vertex
      fintype := D.fintype
      adj := adj π
      decidableAdj := by infer_instance
      symmetric := by
        intro u v
        simp only [adj]
        tauto }
  have hcard (π : P) : @Fintype.card (graph π).vertex (graph π).fintype =
      @Fintype.card D.vertex D.fintype := rfl
  have hloop (π : P) : ∀ v, ¬ (graph π).adj v v := by
    intro v hv
    rcases hv with ⟨h, _⟩ | ⟨h, _⟩ <;> exact (lt_irrefl _ h)
  have hclique (π : P) : ¬ Nonempty (CliqueWitness (graph π) s) := by
    intro hc
    rcases hc with ⟨c⟩
    let b : Fin s → Fin n := fun i => ord π (c.vertex i)
    have hb : Function.Injective b := by
      intro i j hij
      apply c.injective
      apply e.injective
      apply π.injective
      exact hij
    let S : Finset (Fin n) := Finset.univ.image b
    have hS : S.card = s := by
      rw [Finset.card_image_of_injective _ hb, Finset.card_univ, Fintype.card_fin]
    let o := Finset.orderIsoOfFin S hS
    let v : Fin s → D.vertex := fun i =>
      e.symm (π.symm (o i).val)
    have hv_inj : Function.Injective v := by
      intro i j hij
      have : (o i).val = (o j).val := by
        simpa [v] using congrArg (fun x => π (e x)) hij
      exact o.injective (Subtype.ext this)
    have hv_arc : ∀ ⦃i j : Fin s⦄, i.val < j.val → D.arc (v i) (v j) := by
      intro i j hij
      have ho : (o i).val < (o j).val := o.strictMono hij
      have hi : (o i).val ∈ S := (o i).property
      have hj : (o j).val ∈ S := (o j).property
      rcases Finset.mem_image.mp (show (o i).val ∈ Finset.univ.image b by simpa [S] using hi) with ⟨ii, _, hbi⟩
      rcases Finset.mem_image.mp (show (o j).val ∈ Finset.univ.image b by simpa [S] using hj) with ⟨jj, _, hbj⟩
      have hadj : (graph π).adj (c.vertex ii) (c.vertex jj) := by
        apply c.adjacent
        intro heq
        apply ho.ne
        rw [← hbi, ← hbj]
        simp [b, ord, heq]
      rcases hadj with hadj | hadj
      · have hvi : v i = c.vertex ii := by
          dsimp [v]
          rw [← hbi]
          simp only [b, ord]
          rw [π.symm_apply_apply]
          rw [e.symm_apply_apply]
        have hvj : v j = c.vertex jj := by
          dsimp [v]
          rw [← hbj]
          simp only [b, ord]
          rw [π.symm_apply_apply]
          rw [e.symm_apply_apply]
        rw [hvi, hvj]
        exact hadj.2
      · have hback : (o j).val < (o i).val := by
          calc
            (o j).val = b jj := hbj.symm
            _ = ord π (c.vertex jj) := rfl
            _ < ord π (c.vertex ii) := hadj.1
            _ = b ii := rfl
            _ = (o i).val := hbi
        exact False.elim ((not_lt_of_ge (le_of_lt ho)) hback)
    exact hfree ⟨{ vertex := v, injective := hv_inj, forwardArc := hv_arc }⟩
  let ip (π : P) (S : Finset D.vertex) : Prop :=
    S.card = k ∧ ∀ ⦃u v : D.vertex⦄, u ∈ S → v ∈ S → u ≠ v →
      ¬ (graph π).adj u v
  have hind (π : P) :
      IndependentSetCount (graph π) k =
        Fintype.card { S : Finset D.vertex // ip π S } := by
    unfold IndependentSetCount
    let q : Finset (graph π).vertex → Prop := fun S =>
      S.card = k ∧ ∀ ⦃u v : (graph π).vertex⦄, u ∈ S → v ∈ S → u ≠ v →
        ¬ (graph π).adj u v
    have he : Fintype.card {S : Finset (graph π).vertex // q S} =
        Fintype.card {S : Finset D.vertex // ip π S} := by
      apply Fintype.card_congr
      exact Equiv.refl _
    simpa [q, ip] using he.symm
  let fp (f : Fin k → D.vertex) : Prop :=
    ∀ ⦃i j : Fin k⦄, i.val < j.val → ¬ D.arc (f i) (f j)
  let inc (π : P) (f : Fin k → D.vertex) : Prop :=
    ∀ ⦃i j : Fin k⦄, i.val < j.val → ord π (f i) < ord π (f j)
  let ev (π : P) (f : Fin k → D.vertex) : Prop := fp f ∧ inc π f
  have hfwd : ForwardIndependentCount D k =
      Fintype.card { f : Fin k → D.vertex // fp f } := by
    simp [ForwardIndependentCount, fp]
  let sortedTuple (π : P) (S : Finset D.vertex) (hS : S.card = k) :
      Fin k → D.vertex :=
    let T := S.image (ord π)
    let hT : T.card = k := by
      dsimp [T]
      have hord : Function.Injective (ord π) :=
        π.injective.comp e.injective
      rw [Finset.card_image_of_injective _ hord, hS]
    let o := Finset.orderIsoOfFin T hT
    fun i => e.symm (π.symm (o i).val)
  have htuple_mem : ∀ (π : P) (S : Finset D.vertex) (hS : S.card = k)
      (i : Fin k), sortedTuple π S hS i ∈ S := by
    intro π S hS i
    let T : Finset (Fin n) := S.image (ord π)
    have hT : T.card = k := by
      dsimp [T]
      have hord : Function.Injective (ord π) :=
        π.injective.comp e.injective
      rw [Finset.card_image_of_injective _ hord, hS]
    let o := Finset.orderIsoOfFin T hT
    have ho : (o i).val ∈ T := (o i).property
    rcases Finset.mem_image.mp (show (o i).val ∈ S.image (ord π) by
        simpa [T] using ho) with ⟨x, hxS, hx⟩
    have heq : e.symm (π.symm (o i).val) = (x : D.vertex) := by
      apply e.injective
      rw [← hx, Equiv.symm_apply_apply, e.apply_symm_apply]
    have hdef : sortedTuple π S hS i = e.symm (π.symm (o i).val) := by
      rfl
    rw [hdef, heq]
    exact hxS
  have htuple_inc : ∀ (π : P) (S : Finset D.vertex) (hS : S.card = k),
      inc π (sortedTuple π S hS) := by
    intro π S hS i j hij
    let T : Finset (Fin n) := S.image (ord π)
    have hT : T.card = k := by
      have hord : Function.Injective (ord π) :=
        π.injective.comp e.injective
      dsimp [T]
      rw [Finset.card_image_of_injective _ hord, hS]
    let o := Finset.orderIsoOfFin T hT
    have hval : ∀ l : Fin k, ord π (sortedTuple π S hS l) = (o l).val := by
      intro l
      dsimp [ord, sortedTuple, T, o]
      rw [e.apply_symm_apply, π.apply_symm_apply]
    rw [show ord π (sortedTuple π S hS i) = (o i).val by exact hval i,
      show ord π (sortedTuple π S hS j) = (o j).val by exact hval j]
    exact o.strictMono hij
  have hgood : ∀ (π : P) (S : {S : Finset D.vertex // ip π S}),
      ev π (sortedTuple π S S.property.1) := by
    intro π S
    let hS := S.property.1
    constructor
    · intro i j hij ha
      have hi := htuple_mem π S hS i
      have hj := htuple_mem π S hS j
      have hne : sortedTuple π S hS i ≠ sortedTuple π S hS j := by
        intro heq
        have hlt := htuple_inc π S hS hij
        rw [heq] at hlt
        exact (lt_irrefl _ hlt)
      have hna := S.property.2 hi hj hne
      apply hna
      change (ord π (sortedTuple π S hS i) <
          ord π (sortedTuple π S hS j) ∧
          D.arc (sortedTuple π S hS i) (sortedTuple π S hS j)) ∨
        (ord π (sortedTuple π S hS j) <
          ord π (sortedTuple π S hS i) ∧
          D.arc (sortedTuple π S hS j) (sortedTuple π S hS i))
      exact Or.inl ⟨htuple_inc π S hS hij, ha⟩
    · exact htuple_inc π S hS
  have hmap : ∀ π : P,
      Function.Injective (fun S : {S : Finset D.vertex // ip π S} =>
        (⟨sortedTuple π S S.property.1,
          hgood π S⟩ :
          {f : Fin k → D.vertex // ev π f})) := by
    intro π S₁ S₂ heq
    have himage : ∀ S : {S : Finset D.vertex // ip π S},
        Finset.image (sortedTuple π S S.property.1) Finset.univ = S := by
      intro S
      have hScard : (S : Finset D.vertex).card = k := S.property.1
      let T : Finset (Fin n) := (S : Finset D.vertex).image (ord π)
      have hT : T.card = k := by
        dsimp [T]
        have hord : Function.Injective (ord π) :=
          π.injective.comp e.injective
        rw [Finset.card_image_of_injective _ hord, hScard]
      let o := Finset.orderIsoOfFin T hT
      have hval : ∀ l : Fin k, ord π (sortedTuple π S hScard l) =
          (o l).val := by
        intro l
        dsimp [ord, sortedTuple, T, o]
        rw [e.apply_symm_apply, π.apply_symm_apply]
      have htinj : Function.Injective (sortedTuple π S S.property.1) := by
        intro i j hij
        have h' := congrArg (ord π) hij
        rw [hval i, hval j] at h'
        apply o.injective
        apply Subtype.ext
        exact h'
      have hsub : Finset.image (sortedTuple π S S.property.1) Finset.univ ⊆
          (S : Finset D.vertex) := by
        apply Finset.image_subset_iff.mpr
        intro i hi
        exact htuple_mem π S S.property.1 i
      apply Finset.eq_of_subset_of_card_le hsub
      calc
        (S : Finset D.vertex).card = k := hScard
        _ ≤ (Finset.image (sortedTuple π S S.property.1) Finset.univ).card := by
          rw [Finset.card_image_of_injective _ htinj, Finset.card_univ,
            Fintype.card_fin]
    apply Subtype.ext
    rw [← himage S₁, ← himage S₂]
    congr 1
    exact congrArg Subtype.val heq
  have hinj : ∀ (f : Fin k → D.vertex) (π : P), ev π f →
      Function.Injective (fun i => ord π (f i)) := by
    intro f π hπ i j hij
    by_contra hne
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact (ne_of_lt (hπ.2 hlt)) hij
    · exact (ne_of_lt (hπ.2 hgt)) hij.symm
  let emb (f : Fin k → D.vertex) (π : P) (hπ : ev π f) :
      Fin k ↪ Fin n :=
    { toFun := fun i => ord π (f i)
      inj' := hinj f π hπ }
  let q (f : Fin k → D.vertex) (π : P) (hπ : ev π f)
      (τ : Equiv.Perm (Fin k)) : Equiv.Perm (Fin n) :=
    τ.extendDomain (Equiv.ofInjective (emb f π hπ) (emb f π hπ).injective)
  have hq : ∀ (f : Fin k → D.vertex) (π : P) (hπ : ev π f)
      (τ : Equiv.Perm (Fin k)) (i : Fin k),
      q f π hπ τ (ord π (f i)) = ord π (f (τ i)) := by
    intro f π hπ τ i
    have h := Equiv.Perm.extendDomain_apply_image τ
      (Equiv.ofInjective (emb f π hπ) (emb f π hπ).injective) i
    simpa [q, emb] using h
  let phi (f : Fin k → D.vertex)
      (x : {π : P // ev π f} × Equiv.Perm (Fin k)) : P :=
    q f x.1.1 x.1.2 x.2 * x.1.1
  have hphi : ∀ (f : Fin k → D.vertex),
      Function.Injective (phi f) := by
    intro f x y hxy
    rcases x with ⟨⟨π, hπ⟩, τ⟩
    rcases y with ⟨⟨π', hπ'⟩, τ'⟩
    dsimp [phi] at hxy ⊢
    have hout (i : Fin k) :
        ord π (f (τ i)) = ord π' (f (τ' i)) := by
      have h := congrArg (fun r => r (e (f i))) hxy
      rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply] at h
      calc
        ord π (f (τ i)) = q f π hπ τ (ord π (f i)) :=
          (hq f π hπ τ i).symm
        _ = q f π hπ τ (π (e (f i))) := rfl
        _ = q f π' hπ' τ' (π' (e (f i))) := h
        _ = q f π' hπ' τ' (ord π' (f i)) := rfl
        _ = ord π' (f (τ' i)) := hq f π' hπ' τ' i
    have himage : Finset.univ.image (fun i => ord π (f i)) =
        Finset.univ.image (fun i => ord π' (f i)) := by
      calc
        Finset.univ.image (fun i => ord π (f i)) =
            Finset.univ.image (fun i => ord π (f (τ i))) := by
          apply Finset.ext
          intro z
          constructor
          · intro hz
            rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
            obtain ⟨j, hj⟩ := τ.surjective i
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [hj]
              ⟩
          · intro hz
            rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
            exact Finset.mem_image.mpr ⟨τ i, Finset.mem_univ _, rfl⟩
        _ = Finset.univ.image (fun i => ord π' (f (τ' i))) := by
          apply Finset.image_congr
          intro i hi
          exact hout i
        _ = Finset.univ.image (fun i => ord π' (f i)) := by
          apply Finset.ext
          intro z
          constructor
          · intro hz
            rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
            exact Finset.mem_image.mpr ⟨τ' i, Finset.mem_univ _, rfl⟩
          · intro hz
            rcases Finset.mem_image.mp hz with ⟨i, _, rfl⟩
            obtain ⟨j, hj⟩ := τ'.surjective i
            exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, by rw [hj]
              ⟩
    have hcard : (Finset.univ.image (fun i => ord π (f i))).card = k := by
      rw [Finset.card_image_of_injective _ (hinj f π hπ), Finset.card_univ,
        Fintype.card_fin]
    have hcard' : (Finset.univ.image (fun i => ord π' (f i))).card = k := by
      rw [← himage]
      exact hcard
    have hmono : StrictMono (fun i => ord π (f i)) := fun i j hij => hπ.2 hij
    have hmono' : StrictMono (fun i => ord π' (f i)) :=
      fun i j hij => hπ'.2 hij
    have hcan := Finset.orderEmbOfFin_unique hcard
      (fun i => Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩) hmono
    have hcan' := Finset.orderEmbOfFin_unique (s :=
        Finset.univ.image (fun i => ord π (f i))) hcard
      (fun i => by
        have hi : ord π' (f i) ∈
            Finset.univ.image (fun i => ord π' (f i)) :=
          Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
        rw [← himage] at hi
        exact hi) hmono'
    have hg : (fun i => ord π (f i)) = (fun i => ord π' (f i)) := by
      rw [hcan, hcan']
    have hτ : τ = τ' := by
      apply Equiv.ext
      intro i
      apply (hinj f π hπ)
      calc
        ord π (f (τ i)) = ord π' (f (τ' i)) := hout i
        _ = ord π (f (τ' i)) := (congrFun hg (τ' i)).symm
    have hqeq : q f π hπ τ = q f π' hπ' τ' := by
      apply Equiv.Perm.ext
      intro z
      by_cases hz : z ∈ Finset.univ.image (fun i => ord π (f i))
      · rcases Finset.mem_image.mp hz with ⟨i, _, hi⟩
        have hz' : z ∈ Finset.univ.image (fun i => ord π' (f i)) := by
          rw [← himage]
          exact hz
        rcases Finset.mem_image.mp hz' with ⟨j, _, hj⟩
        have hij : i = j := by
          apply (hinj f π hπ)
          calc
            ord π (f i) = z := hi
            _ = ord π' (f j) := hj.symm
            _ = ord π (f j) := (congrFun hg j).symm
        calc
          (q f π hπ τ) z = (q f π hπ τ) (ord π (f i)) := by rw [hi]
          _ = ord π (f (τ i)) := hq f π hπ τ i
          _ = ord π (f (τ' j)) := by rw [hτ, hij]
          _ = ord π' (f (τ' j)) := congrFun hg (τ' j)
          _ = (q f π' hπ' τ') (ord π' (f j)) :=
            (hq f π' hπ' τ' j).symm
          _ = (q f π' hπ' τ') z := by rw [hj]
      · have hz' : z ∉ Finset.univ.image (fun i => ord π' (f i)) := by
          intro hz'
          apply hz
          rw [himage]
          exact hz'
        have hr : z ∉ Set.range (emb f π hπ) := by
          intro hr
          rcases hr with ⟨i, rfl⟩
          exact hz (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        have hr' : z ∉ Set.range (emb f π' hπ') := by
          intro hr'
          rcases hr' with ⟨i, rfl⟩
          exact hz' (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
        rw [show q f π hπ τ z = z by
          dsimp [q]
          exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hr,
          show q f π' hπ' τ' z = z by
          dsimp [q]
          exact Equiv.Perm.extendDomain_apply_not_subtype _ _ hr']
    rw [hqeq] at hxy
    have hπeq : π = π' := mul_left_cancel hxy
    cases hπeq
    cases hτ
    rfl
  have hcount : ∀ f : Fin k → D.vertex,
      Fintype.card {π : P // ev π f} * Nat.factorial k ≤ Nat.factorial n := by
    intro f
    calc
      Fintype.card {π : P // ev π f} * Nat.factorial k =
          Fintype.card ({π : P // ev π f} × Equiv.Perm (Fin k)) := by
        rw [Fintype.card_prod, Fintype.card_perm, Fintype.card_fin]
      _ ≤ Fintype.card P := Fintype.card_le_of_injective (phi f) (hphi f)
      _ = Nat.factorial n := by
        dsimp [P]
        rw [Fintype.card_perm, Fintype.card_fin]
  have hcount' : ∀ f : Fin k → D.vertex,
      Fintype.card {π : P // ev π f} * Nat.factorial k ≤
        if fp f then Nat.factorial n else 0 := by
    intro f
    by_cases hf : fp f
    · simp [hf]
      exact hcount f
    · haveI : IsEmpty {π : P // ev π f} :=
        ⟨fun x => hf x.property.1⟩
      simp [hf, Fintype.card_eq_zero]
  have hcard_fp :
      Fintype.card {f : Fin k → D.vertex // fp f} =
        ∑ f : Fin k → D.vertex, if fp f then 1 else 0 := by
    rw [Fintype.card_of_subtype (Finset.univ.filter fp) (by
      intro f
      simp)]
    rw [Finset.card_filter]
  have hsum_f :
      (∑ f : Fin k → D.vertex, Fintype.card {π : P // ev π f}) *
          Nat.factorial k ≤
        Fintype.card {f : Fin k → D.vertex // fp f} * Nat.factorial n := by
    calc
      (∑ f : Fin k → D.vertex, Fintype.card {π : P // ev π f}) *
            Nat.factorial k =
          ∑ f : Fin k → D.vertex,
            Fintype.card {π : P // ev π f} * Nat.factorial k := by
        rw [Finset.sum_mul]
      _ ≤ ∑ f : Fin k → D.vertex, if fp f then Nat.factorial n else 0 := by
        apply Finset.sum_le_sum
        intro f hf
        exact hcount' f
      _ = Fintype.card {f : Fin k → D.vertex // fp f} * Nat.factorial n := by
        calc
          (∑ f : Fin k → D.vertex, if fp f then Nat.factorial n else 0) =
              ∑ f : Fin k → D.vertex,
                (if fp f then 1 else 0) * Nat.factorial n := by
            apply Finset.sum_congr rfl
            intro f hf
            by_cases hfp : fp f <;> simp [hfp]
          _ = (∑ f : Fin k → D.vertex, if fp f then 1 else 0) *
                Nat.factorial n := by rw [Finset.sum_mul]
          _ = Fintype.card {f : Fin k → D.vertex // fp f} *
                Nat.factorial n := by rw [hcard_fp]
  have hsum_ind :
      (∑ π : P, Fintype.card {S : Finset D.vertex // ip π S}) ≤
        ∑ π : P, Fintype.card {f : Fin k → D.vertex // ev π f} := by
    apply Finset.sum_le_sum
    intro π hπ
    exact Fintype.card_le_of_injective _ (hmap π)
  have hsubcard : ∀ {α : Type} [Fintype α] (p : α → Prop) [DecidablePred p],
      Fintype.card {x : α // p x} = ∑ x : α, if p x then 1 else 0 := by
    intro α _ p dp
    rw [Fintype.card_of_subtype (Finset.univ.filter p) (by
      intro x
      simp)]
    rw [Finset.card_filter]
  have hdouble :
      (∑ π : P, Fintype.card {f : Fin k → D.vertex // ev π f}) =
        ∑ f : Fin k → D.vertex, Fintype.card {π : P // ev π f} := by
    calc
      (∑ π : P, Fintype.card {f : Fin k → D.vertex // ev π f}) =
          ∑ π : P, ∑ f : Fin k → D.vertex, if ev π f then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro π hπ
        simpa using (hsubcard (p := ev π))
      _ = ∑ f : Fin k → D.vertex, ∑ π : P, if ev π f then 1 else 0 := by
        exact Finset.sum_comm
      _ = ∑ f : Fin k → D.vertex, Fintype.card {π : P // ev π f} := by
        apply Finset.sum_congr rfl
        intro f hf
        simpa using (hsubcard (p := fun π : P => ev π f)).symm
  have hsum_pi_bound :
      (∑ π : P, Fintype.card {S : Finset D.vertex // ip π S}) *
          Nat.factorial k ≤
        Fintype.card {f : Fin k → D.vertex // fp f} * Nat.factorial n := by
    calc
      (∑ π : P, Fintype.card {S : Finset D.vertex // ip π S}) *
            Nat.factorial k ≤
          (∑ π : P, Fintype.card {f : Fin k → D.vertex // ev π f}) *
            Nat.factorial k :=
        Nat.mul_le_mul_right _ hsum_ind
      _ = (∑ f : Fin k → D.vertex, Fintype.card {π : P // ev π f}) *
            Nat.factorial k := by rw [hdouble]
      _ ≤ Fintype.card {f : Fin k → D.vertex // fp f} * Nat.factorial n := hsum_f
  have hreal :
      (∑ π : P, (Fintype.card {S : Finset D.vertex // ip π S} : ℝ)) *
          (Nat.factorial k : ℝ) ≤
        (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) *
          (Nat.factorial n : ℝ) := by
    exact_mod_cast hsum_pi_bound
  have hex : ∃ π : P,
      (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) ≤
        (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
          (Nat.factorial k : ℝ) := by
    by_contra h
    have hno : ∀ π : P,
        ¬ (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) ≤
          (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
            (Nat.factorial k : ℝ) := by
      intro π hπ
      exact h ⟨π, hπ⟩
    have hlt : ∀ π : P,
        (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
            (Nat.factorial k : ℝ) <
          (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) := by
      intro π
      exact lt_of_not_ge (hno π)
    have hP : (Finset.univ : Finset P).Nonempty := by
      exact ⟨Equiv.refl _, Finset.mem_univ _⟩
    have hlt_sum :
        (∑ _π : P,
            (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
              (Nat.factorial k : ℝ)) <
          ∑ π : P, (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) := by
      apply Finset.sum_lt_sum_of_nonempty hP
      intro π hπ
      exact hlt π
    have hPcard : Fintype.card P = Nat.factorial n := by
      dsimp [P]
      rw [Fintype.card_perm, Fintype.card_fin]
    have hlt_sum' :
        (Nat.factorial n : ℝ) *
            ((Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
              (Nat.factorial k : ℝ)) <
          ∑ π : P, (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) := by
      simpa [Finset.sum_const, hPcard] using hlt_sum
    have hkfac : (0 : ℝ) < Nat.factorial k := by positivity
    have hlt_div :
        (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) *
            (Nat.factorial n : ℝ) /
              (Nat.factorial k : ℝ) <
          ∑ π : P, (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) := by
      convert hlt_sum' using 1 <;> ring
    have hlt_mul := (div_lt_iff₀ hkfac).mp hlt_div
    exact (not_lt_of_ge hreal) hlt_mul
  rcases hex with ⟨π, hπ⟩
  refine ⟨graph π, hcard π, hloop π, hclique π, ?_⟩
  rw [hind π]
  have hfac_inv :
      1 / (Nat.factorial k : ℝ) ≤ (Real.exp 1 / (k : ℝ)) ^ k := by
    have hkR : (1 : ℝ) ≤ k := by exact_mod_cast hk
    have hsarg : (1 : ℝ) ≤ 2 * Real.pi * (k : ℝ) := by
      have hp := Real.two_le_pi
      nlinarith
    have hs : (1 : ℝ) ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) :=
      (Real.one_le_sqrt).2 hsarg
    have hfac : ((k : ℝ) / Real.exp 1) ^ k ≤ (Nat.factorial k : ℝ) := by
      calc
        ((k : ℝ) / Real.exp 1) ^ k =
            1 * ((k : ℝ) / Real.exp 1) ^ k := by ring
        _ ≤ Real.sqrt (2 * Real.pi * (k : ℝ)) *
              ((k : ℝ) / Real.exp 1) ^ k := by gcongr
        _ ≤ (Nat.factorial k : ℝ) := Stirling.le_factorial_stirling k
    have hpos : 0 < ((k : ℝ) / Real.exp 1) ^ k := by positivity
    have hi := one_div_le_one_div_of_le hpos hfac
    calc
      1 / (Nat.factorial k : ℝ) ≤
          1 / (((k : ℝ) / Real.exp 1) ^ k) := hi
      _ = (Real.exp 1 / (k : ℝ)) ^ k := by
        have hk0 : (k : ℝ) ≠ 0 := by positivity
        have he0 : Real.exp 1 ≠ 0 := ne_of_gt (Real.exp_pos 1)
        field_simp [hk0, he0]
        rw [← mul_pow]
        field_simp [hk0, he0]
        norm_num
  have hnonneg :
      0 ≤ (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) := by positivity
  have hmain :
      (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) ≤
        (Real.exp 1 / (k : ℝ)) ^ k *
          (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) := by
    calc
      (Fintype.card {S : Finset D.vertex // ip π S} : ℝ) ≤
          (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) /
            (Nat.factorial k : ℝ) := hπ
      _ = (1 / (Nat.factorial k : ℝ)) *
            (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) := by ring
      _ ≤ (Real.exp 1 / (k : ℝ)) ^ k *
            (Fintype.card {f : Fin k → D.vertex // fp f} : ℝ) := by
        gcongr
  rw [hfwd]
  exact hmain
