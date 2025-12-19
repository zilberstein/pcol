import Mathlib.Order.CompletePartialOrder

import Pcol.Semantics.Lpo.Basic

variable {l : Type} [LE l] [Bot l]

structure LE_Lpo (a b : Lpo l) : Prop where
  nodes : a.nodes ⊆ b.nodes
  downcl : b.rel.is_down_closed a.nodes
  rel : ∀ x ∈ a.nodes, ∀ y ∈ a.nodes, a.rel x y = b.rel x y
  lab : ∀ x, a.lab x ≤ b.lab x
  form : ∀ x ∈ a.nodes, a.form x = b.form x
  succ : ∀ x ∈ b.nodes, x ∈ a.nodes ∨ ∃ z ∈ a.bots, b.rel z x

instance : LE (Lpo l) where
  le a b := LE_Lpo a b

lemma le_rel {a b : Lpo l} (h : a ≤ b)
    {x y : Node} : a.rel x y → b.rel x y := by
  intro hxy; obtain ⟨hx, hy⟩ := a.property.rel_dom hxy
  exact (h.rel _ hx _ hy).mp hxy

lemma le_same_root {α β : Lpo l} (hle : α ≤ β) :
    ∃ x ∈ α.nodes,
      (∀ y ∈ α.nodes, x ≠ y → α.rel x y) ∧
      ∀ z ∈ β.nodes, x ≠ z → β.rel x z := by
  obtain ⟨x, hx, hroot⟩ := α.property.rel.single_rooted
  refine ⟨x, hx, hroot, fun z hz hneq ↦ ?_⟩
  obtain ⟨y, hy, hroot'⟩ := β.property.rel.single_rooted
  by_cases hxy : x = y
  · subst hxy; exact hroot' _ hz hneq
  · exfalso
    have hyx := hroot' _ (hle.nodes hx) (Ne.symm hxy)
    refine hxy (β.property.rel.antisymm ?_ hyx)
    have hy' := hle.downcl x hx y hyx
    exact (hle.rel _ hx _ hy').mp (hroot _ hy' hxy)

lemma le_form {α β : Lpo l} (hle : α ≤ β) {x : Node} :
    α.form x ≤ β.form x := by
  by_cases hx : x ∈ α.nodes
  · exact le_of_eq (hle.form x hx)
  · refine le_of_eq_of_le (b := Form.false) ?_ ?_
    · ext v; constructor
      · intro c; refine (α.property.form_dom x).not.mpr hx ?_; exact ⟨v, c⟩
      · intro c; exfalso; exact c
    · intro v c; exfalso; exact c

variable {l : Type} [PartialOrder l] [OrderBot l]

instance : Preorder (Lpo l) where
  le_refl a := by {
    constructor <;> try simp
    · intro _ _ _ hr; exact (a.property.rel_dom hr).1
    · intro _ hx; left; exact hx
    }
  le_trans a b c := by {
    intro hab hbc;
    have hsub := subset_trans hab.nodes hbc.nodes
    constructor
    · exact hsub
    · intro x hx y hyx
      have h := hbc.downcl x (hab.nodes hx) y hyx
      rw [← hbc.rel y h x (hab.nodes hx)] at hyx
      exact hab.downcl x hx y hyx
    · intro x hx y hy; rw [hab.rel _ hx _ hy, hbc.rel _ (hab.nodes hx) _ (hab.nodes hy)]
    · intro x; refine le_trans (hab.lab _) ?_; exact hbc.lab _
    · intro x hx; refine Eq.trans (hab.form _ hx) ?_
      exact hbc.form _ (hab.nodes hx)
    · intro x hx
      rcases hbc.succ _ hx with hb | ⟨z, hz, hzx⟩
      · rcases hab.succ _ hb with ha | ⟨z, hz, hzx⟩
        · left; exact ha
        · right; exact ⟨z, hz, le_rel hbc hzx⟩
      · right; rcases hab.succ _ hz.1 with ha | ⟨w, hw, hwz⟩
        · refine ⟨z, ⟨ha, ?_⟩, hzx⟩
          exact bot_unique (le_of_le_of_eq (hab.lab z) hz.2)
        · exact ⟨w, hw, c.property.rel.trans (le_rel hbc hwz) hzx⟩
  }

instance : PartialOrder (Lpo l) where
  le_antisymm a b := by {
    intro hab hba
    have heq := le_antisymm hab.nodes hba.nodes
    refine lpo_eq_iff.2 ?_
    refine ⟨heq, ?_, ?_, ?_⟩
    · ext x y; by_cases hx : x ∈ a.nodes
      · by_cases hy : y ∈ a.nodes
        · rw [hab.rel _ hx _ hy]
        · rw [eq_false (a.not_in_dom_not_rel x y (Or.inr hy))]
          rw [heq] at hy
          rw [eq_false (b.not_in_dom_not_rel x y (Or.inr hy))]
      · rw [eq_false (a.not_in_dom_not_rel x y (Or.inl hx))]
        rw [heq] at hx
        rw [eq_false (b.not_in_dom_not_rel x y (Or.inl hx))]
    · ext x; by_cases hxa : x ∈ a.nodes
      · have hxb : x ∈ b.nodes := by rw [heq] at hxa; exact hxa
        exact le_antisymm (hab.lab x) (hba.lab x)
      · rw [Lpo.lab, a.property.lab_dom _ hxa]
        rw [heq] at hxa; rw [Lpo.lab, b.property.lab_dom _ hxa]
    · ext1 x; by_cases hx : x ∈ a.nodes
      · exact hab.form x hx
      · have ha := not_exists.mp ((a.property.form_dom x).not.mpr hx)
        have hx' : x ∉ b.nodes := by
          intro c; exact hx ((congrArg₂ (· ∈ ·) rfl heq).mpr c)
        have hb := not_exists.mp ((b.property.form_dom x).not.mpr hx')
        ext v; constructor
        · intro c; exfalso; exact ha v c
        · intro c; exfalso; exact hb v c
  }

variable {l : Type} [CompletePartialOrder l] [OrderBot l]

def lpo_base_sup (s : Set (Lpo l)) : Lpo_base l := {
  nodes := ⋃ a ∈ s, a.nodes
  rel x y := ∃ a ∈ s, a.rel x y
  lab x := sSup { l | ∃ a ∈ s, l = a.lab x }
  form x v := ∃ a ∈ s, a.form x v
}

instance {l : Type} [Bot l] : Inhabited (Lpo l) where
  default := Lpo.singleton default ⊥

noncomputable instance : SupSet (Lpo l) where
  sSup s : Lpo l := by {
    by_cases h : is_valid_lpo (lpo_base_sup s)
    · exact ⟨lpo_base_sup s, h⟩
    · exact default
  }

lemma lpo_directed_same_root {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) :
    ∃ x, ∀ α ∈ d, x ∈ α.nodes ∧ ∀ y ∈ α.nodes, x ≠ y → α.rel x y := by
  obtain ⟨α, hα⟩ := hne
  obtain ⟨x, hx, hroot⟩ := α.property.rel.single_rooted
  use x; intro β hβ
  obtain ⟨γ, hγ, hαγ, hβγ⟩ := hd _ hα _ hβ
  obtain ⟨y, hy, hyα, hyγ⟩ := le_same_root hαγ
  obtain ⟨z, hz, hzβ, hzγ⟩ := le_same_root hβγ
  have hxy : x = y := by
    by_contra hc; refine hc (α.property.rel.antisymm ?_ ?_)
    · exact hroot _ hy hc
    · exact hyα _ hx (Ne.symm hc)
  subst hxy
  have hxz : x = z := by
    by_contra hc; refine hc (γ.property.rel.antisymm ?_ ?_)
    · exact hyγ _ (hβγ.nodes hz) hc
    · exact hzγ _ (hαγ.nodes hx) (Ne.symm hc)
  subst hxz; exact ⟨hz, hzβ⟩

-- Is this not in Mathlib?
lemma directed_finite_upper_bound {d : Set (Lpo l)} (h : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty)
    {s : Set (Lpo l)} (hsub : s ⊆ d) (hfin : s.Finite) :
    ∃ α ∈ d, ∀ β ∈ s, β ≤ α := by
  refine hfin.induction_on_subset s ?_ ?_
  · obtain ⟨α, hα⟩ := hne
    refine ⟨α, hα, ?_⟩; intro β hc; exfalso; exact hc
  · intro α t hα hst hnt ⟨β, hβ, hub⟩
    obtain ⟨γ, hγ, hαγ, hβγ⟩ := h _ (hsub hα) _ hβ
    refine ⟨γ, hγ, ?_⟩; intro γ' hγ'
    rcases Set.mem_insert_iff.mp hγ' with rfl | ht
    · exact hαγ
    · exact (hub _ ht).trans hβγ

lemma lev_isotone {l : Type} [Bot l] [LE l] {a b : Lpo l} {x : Node}
    (hle : a ≤ b) (hx : x ∈ a.nodes) : a.rel.lev x = b.rel.lev x := by
    refine congrArg sSup ?_; ext _; simp only [Set.mem_setOf_eq]
    refine exists_congr (fun n ↦ and_congr_right ?_); rintro rfl
    refine exists_congr (fun c ↦ and_congr_left ?_); rintro rfl
    constructor
    · intro hc k; exact le_rel hle (hc k)
    · intro hc k; refine (hle.rel _ ?_ _ ?_).mpr (hc k)
      · refine hle.downcl _ hx _ ?_; refine succ_chain_mono _ hc ?_
        exact Fin.lt_def.mpr k.isLt
      · by_cases heq : k.succ = Fin.last n
        · refine (congrArg₂ Membership.mem rfl (congrArg _ heq)).mpr hx
        · refine hle.downcl _ hx _ ?_; refine succ_chain_mono _ hc ?_
          refine Fin.lt_def.mpr ?_; simp only [Fin.val_last]
          refine lt_of_le_of_ne (Nat.succ_le_of_lt k.isLt) ?_
          exact (Fin.val_eq_val _ _).mp.mt heq

lemma lpo_directed_lev_eq {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d)
    (x : Node) : ∃ n : ℕ, ∀ α ∈ d, x ∈ α.nodes → α.rel.lev x = n := by
  by_cases h : ∃ α ∈ d, x ∈ α.nodes
  · obtain ⟨α, hα, hx⟩ := h
    obtain ⟨n, hn⟩ := lev_finite hx
    use n; intro β hβ hx'; rw [← hn]
    obtain ⟨γ, hγ, hαγ, hβγ⟩ := hd _ hα _ hβ
    refine (lev_isotone hβγ hx').trans ?_
    exact (lev_isotone hαγ hx).symm
  · simp only [not_exists, not_and] at h; use 0
    intro α hα hx; exfalso; exact h _ hα hx

lemma lpo_directed_exists_preds {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty)
    {s : Set Node} (hfin : s.Finite) :
    ∃ α ∈ d, ∀ x ∈ s, α.lab x ≠ ⊥ ∨ ∀ γ ∈ d, γ.lab x = ⊥ := by
  have h' : ∀ x ∈ s, ∃ α ∈ d, α.lab x ≠ ⊥ ∨ ∀ β ∈ d, β.lab x = ⊥ := by
    intro x hx; by_cases hlab : ∃ β ∈ d, β.lab x ≠ ⊥
    · obtain ⟨β, hβ, hlab⟩ := hlab; exact ⟨β, hβ, Or.inl hlab⟩
    · simp only [ne_eq, not_exists, not_and, not_not] at hlab
      obtain ⟨α, hα⟩ := hne; exact ⟨α, hα, Or.inr hlab⟩
  choose g hg using h'
  let A : Set (Lpo l):= (fun x ↦ g x.val x.property) '' (Set.univ : Set ↑s)
  have hfin' : A.Finite := (Set.finite_univ_iff.mpr hfin).image _
  have hsub : A ⊆ d := by
    intro α hα; simp [A] at hα
    rcases hα with ⟨x, hx, rfl⟩; exact (hg x hx).1
  obtain ⟨α, hα, hub⟩ := directed_finite_upper_bound hd hne hsub hfin'
  refine ⟨α, hα, ?_⟩; intro x hx
  rcases hg x hx with ⟨hmem, hlab | hlab⟩
  · left; refine ne_of_gt (lt_of_lt_of_le ?_ ?_ (b := (g x hx).lab x))
    · exact lt_of_le_of_ne bot_le (Ne.symm hlab)
    · refine (hub _ ?_).lab x; simp only [Set.image_univ, Set.mem_range, A]
      exact ⟨⟨x, hx⟩, rfl⟩
  · right; exact hlab

-- Lemma C.6 of CONCUR '25
lemma lpo_directed_fin_lev {d : Set (Lpo l)} (h : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) (n : ℕ) :
    ∃ X, X.Finite ∧ X ⊆ ⋃ α ∈ d, α.nodes ∧ ∀ α ∈ d, { x ∈ α.nodes | α.rel.lev x = n } ⊆ X := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero =>
      obtain ⟨x, hroot⟩ := lpo_directed_same_root h hne
      refine ⟨{x}, Set.finite_singleton _, ?_, ?_⟩
      · rintro x rfl; obtain ⟨α, hα⟩ := hne
        simp only [Set.mem_iUnion, exists_prop]
        refine ⟨α, hα, (hroot _ hα).1⟩
      · intro α hα y ⟨hy, hlev⟩
        obtain ⟨hx, hroot₁⟩ := hroot α hα
        have hroot₂ := lev_zero hy hlev
        refine Set.mem_singleton_iff.mpr ?_
        by_contra hc; refine hc (α.property.rel.antisymm ?_ ?_)
        · exact hroot₂ _ hx hc
        · exact hroot₁ _ hy (Ne.symm hc)
    | succ n =>
      choose f hf using ih
      let X := ⋃ k : Fin (n + 1), f k.val k.isLt
      have hfin : X.Finite := Set.finite_iUnion (fun k ↦ (hf k.val k.isLt).1)
      obtain ⟨α, hα, hlab⟩ := lpo_directed_exists_preds h hne hfin
      refine ⟨{ x ∈ α.nodes | α.rel.lev x = n + 1 }, ?_, ?_, ?_⟩
      · exact α.property.rel.fin_lev _
      · intro x ⟨hx, _⟩; simp only [Set.mem_iUnion, exists_prop]
        exact ⟨α, hα, hx⟩
      · intro β hβ x ⟨hx, hlev⟩;
        have hx' : x ∈ α.nodes := by
          obtain ⟨γ, hγ, hαγ, hβγ⟩ := h _ hα _ hβ
          rcases hαγ.succ _ (hβγ.nodes hx) with hx' | ⟨y, ⟨hy, hbot⟩, hyx⟩
          · exact hx'
          · exfalso
            have hyl : γ.rel.lev y < n + 1 := by
              refine lt_of_lt_of_eq (lev_mono hyx) ?_
              obtain ⟨k, hk⟩ := lpo_directed_lev_eq h x
              refine (hk _ hγ (γ.property.rel_dom hyx).2).trans ?_
              exact (hk _ hβ hx).symm.trans hlev
            obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp (ne_of_lt (hyl.trans (ENat.coe_lt_top _)))
            have hmn : m < n + 1 := by
              refine ENat.coe_lt_coe.mp ?_; simp [hm, hyl]
            have hy' : y ∈ X := by
              simp only [Set.mem_iUnion, X]; refine ⟨⟨m, hmn⟩, ?_⟩
              exact (hf m hmn).2.2 γ hγ ⟨(γ.property.rel_dom hyx).1, hm.symm⟩
            rcases hlab _ hy' with hlab | hlab
            · exact hlab hbot
            · exact γ.property.bot y (hlab _ hγ) _ hyx
        refine ⟨hx', ?_⟩
        obtain ⟨k, hk⟩ := lpo_directed_lev_eq h x
        refine (hk _ hα hx').trans ((hk _ hβ hx).symm.trans (hlev.trans ?_))
        simp only [Nat.cast_add, Nat.cast_one]

lemma is_succ_chain_directed {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) {n : ℕ}
    {α : Lpo l} {c : FinChain n Node}
    (hα : α ∈ d) (hc : Rel.is_succ_chain (fun x y ↦ ∃ α ∈ d, α.rel x y) c) (hl : c.last ∈ α.nodes) :
    α.rel.is_succ_chain c := by
  -- Key Lemma
  have h (j : Fin n) (hmem : c j.succ ∈ α.nodes) :
      α.rel
        (c ⟨j.val, Nat.lt_add_right _ j.isLt⟩)
        (c ⟨j.val + 1, Nat.add_lt_add_right j.isLt _⟩) := by
    obtain ⟨β, hβ, hrel⟩ := hc j
    obtain ⟨γ, hγ, hαγ, hβγ⟩ := hd _ hα _ hβ
    have hrel' := le_rel hβγ hrel
    refine (hαγ.rel _ ?_ _ hmem).mpr hrel'
    exact hαγ.downcl _ hmem _ hrel'
  intro k; generalize hi : n - (k.val + 1) = i; revert k; induction i with
  | zero =>
    intro k hk; refine h k ?_
    refine (congrArg₂ Membership.mem rfl (congrArg _ ?_)).mp hl
    ext; simp only [Fin.val_last, Fin.val_succ]
    refine le_antisymm ?_ ?_
    · exact Nat.le_of_sub_eq_zero hk
    · exact Nat.succ_le_of_lt k.isLt
  | succ i ih =>
    intro k hk; refine h _ ?_
    refine (α.property.rel_dom (ih ⟨k.val + 1, ?_⟩ ?_)).1
    · refine Nat.lt_of_sub_pos (Nat.lt_of_succ_le ?_); linarith
    · simp only; rw [Nat.sub_add_eq, hk, add_tsub_cancel_right]

lemma lpo_sup_IsCausalityRel {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·) d) (hne : d.Nonempty) :
    (lpo_base_sup d).rel.IsCausalityRel (lpo_base_sup d).nodes := by
  constructor
  -- Transitivity
  · rintro x y z ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
    rcases hd a ha b hb with ⟨c, hc, hac, hbc⟩
    refine ⟨c, hc, ?_⟩
    refine c.property.rel.trans ?_ ?_ (y := y)
    · have hxy := a.property.rel_dom har
      rw [hac.rel _ hxy.1 _ hxy.2] at har
      exact har
    · have hyz := b.property.rel_dom hbr
      rw [hbc.rel _ hyz.1 _ hyz.2] at hbr
      exact hbr
  -- Antisymmetry
  · intro x y ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
    rcases hd a ha b hb with ⟨c, hc, hac, hbc⟩
    have hxy := a.property.rel_dom har
    rw [hac.rel _ hxy.1 _ hxy.2] at har
    have hyx := b.property.rel_dom hbr
    rw [hbc.rel _ hyx.1 _ hyx.2] at hbr
    exact c.property.rel.antisymm har hbr
  -- Irreflexitivity
  · intro x ⟨a, _, hr⟩; exact a.property.rel.irrefl _ hr
  -- Finitely Preceded
  · intro x; by_cases hx : ∃ a ∈ d, x ∈ a.nodes
    · rcases hx with ⟨a, ha, hx⟩; refine (congrArg _ ?_).mp (a.property.rel.fin_prec x)
      ext y; constructor
      · intro hyx; exact ⟨a, ha, hyx⟩
      · intro ⟨b, hb, hyx⟩; obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
        obtain ⟨hby, hbx⟩ := b.property.rel_dom hyx
        rw [hbc.rel _ hby _ hbx] at hyx
        refine (hac.rel _ ?_ _ hx).mpr hyx
        exact hac.downcl _ hx _ hyx
    · refine (congrArg _ ?_).mp Set.finite_empty; ext y; constructor
      · rintro ⟨⟩
      · intro ⟨a, ha, hyx⟩; exfalso; refine hx ⟨a, ha, ?_⟩
        exact (a.property.rel_dom hyx).2
  -- Finite Levels
  · intro n; obtain ⟨X, hfin, _, hub⟩ := lpo_directed_fin_lev hd hne n
    refine hfin.subset ?_; intro x ⟨hx, hlev⟩
    simp only [lpo_base_sup, Set.mem_iUnion, exists_prop] at hx
    rcases hx with ⟨α, hα, hx⟩; refine hub α hα ⟨hx, ?_ ⟩
    obtain ⟨k, hk⟩ := lpo_directed_lev_eq hd x
    refine (hk _ hα hx).trans (Eq.trans ?_ hlev)
    refine le_antisymm (le_sSup ?_) (sSup_le ?_)
    · simp only [Set.mem_setOf_eq, Nat.cast_inj, exists_eq_left']
      obtain ⟨c, hc, hl⟩ := lev_finite_exists_finchain (hk _ hα hx)
      exact ⟨c, fun k' ↦ ⟨α, hα, hc k'⟩, hl⟩
    · rintro _ ⟨m, rfl, c, hc, hl⟩
      have hc' := is_succ_chain_directed hd hα hc ((congrArg₂ Membership.mem rfl hl).mpr hx)
      rw [← hk _ hα hx]; refine le_sSup ?_
      exact ⟨m, rfl, c, hc', hl⟩
  -- Single Rooted
  · rcases hne with ⟨a, ha⟩; rcases a.property.rel.single_rooted with ⟨x, hx, hroot⟩; use x
    simp only [lpo_base_sup, Set.mem_iUnion, exists_prop, ne_eq, forall_exists_index, and_imp]
    refine ⟨⟨a, ha, hx⟩, ?_⟩
    intro y b hb hy hneq; obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
    obtain ⟨z, hz, hroot'⟩ := c.property.rel.single_rooted; by_cases heq : z = x
    · subst heq; exact ⟨c, hc, hroot' y (hbc.nodes hy) hneq⟩
    · exfalso; have hzx := hroot' x (hac.nodes hx) heq
      refine heq (c.property.rel.antisymm hzx ?_)
      have hza := hac.downcl _ hx _ hzx
      exact (hac.rel _ hx _ hza).mp (hroot _ hza (Ne.symm heq))

lemma lpo_lab_directed {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·) d) (x : Node) :
    DirectedOn LE.le {l_1 | ∃ a ∈ d, l_1 = a.lab x} := by
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
  obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
  refine ⟨c.lab x, ⟨c, hc, rfl⟩, hac.lab x, hbc.lab x⟩

lemma form_directed_eq {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·) d) {x : Node} {α β : Lpo l}
    (hα : α ∈ d) (hβ : β ∈ d) (hx : x ∈ α.nodes) (hx' : x ∈ β.nodes) :
    α.form x = β.form x := by
  obtain ⟨γ, _, hαγ, hβγ⟩ := hd _ hα _ hβ
  rw [hαγ.form x hx, hβγ.form x hx']

lemma form_vars_set {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·) d) {x : Node} {α : Lpo l}
    (hα : α ∈ d) (hx : x ∈ α.nodes) :
    Form.vars (fun v ↦ ∃ a ∈ d, a.form x v) = ⋃ a ∈ d, (a.form x).vars := by
  ext y; constructor
  · simp only [Form.vars, Form.free, not_forall, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop,
      forall_exists_index]
    intro v hs
    refine ⟨α, hα, v, not_iff.mpr ⟨?_, ?_⟩⟩
    · intro hform;
      have hform' : ¬ ∃ β ∈ d, β.form x v := by
        simp only [not_exists, not_and]; intro β hβ
        by_cases hx' : x ∈ β.nodes
        · rw [← form_directed_eq hd hα hβ hx hx']; exact hform
        · have hfls := (β.property.form_dom x).mp.mt hx'
          simp only [Form.sat, not_exists] at hfls
          exact hfls _
      obtain ⟨β, hβ, hf⟩ := (not_iff.mp hs).mp hform'
      have hx' := (β.property.form_dom x).mp ⟨_, hf⟩
      rw [form_directed_eq hd hα hβ hx hx']; exact hf
    · intro hform
      have h := (not_iff.mp hs).mpr ⟨α, hα, hform⟩
      simp only [not_exists, not_and] at h
      exact h α hα
  · simp only [Form.vars, Form.free, not_forall, Set.mem_iUnion, Set.mem_setOf_eq, exists_prop,
      forall_exists_index, and_imp]
    intro α hα v hs; use v; refine not_iff.mpr ⟨?_, ?_⟩
    · simp only [not_exists, not_and]
      intro h; refine ⟨α, hα, ?_⟩
      exact (not_iff.mp hs).mp (h α hα)
    · simp only [not_exists, not_and, forall_exists_index, and_imp]
      intro β hβ hform γ hγ; by_cases hxγ : x ∈ γ.nodes
      · have hxα : x ∈ α.nodes := by
          by_contra hc; apply (α.property.form_dom x).mp.mt at hc
          simp only [Form.sat, not_exists] at hc
          exact hc _ ((not_iff.mp hs).mp (hc _))
        have hxβ := (β.property.form_dom x).mp ⟨_, hform⟩
        rw [form_directed_eq hd hβ hα hxβ hxα] at hform
        rw [form_directed_eq hd hγ hα hxγ hxα]
        exact (not_iff.mp hs).mpr hform
      · have hfls := (γ.property.form_dom x).mp.mt hxγ
        simp only [Form.sat, not_exists] at hfls
        exact hfls _

lemma lpo_sup_valid {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·) d) (hne : d.Nonempty) :
    is_valid_lpo (lpo_base_sup d) := by
  unfold lpo_base_sup
  constructor <;> try simp
  -- Relation Domain
  · intro x y a ha hrel
    rcases a.property.rel_dom hrel with ⟨hx, hy⟩
    exact ⟨⟨a, ha, hx⟩, ⟨a, ha, hy⟩⟩
  -- Label Domain
  · intro x hx; refine bot_unique (DirectedOn.sSup_le (lpo_lab_directed hd x) ?_)
    rintro _ ⟨a, ha, rfl⟩; exact le_of_eq (a.property.lab_dom _ (hx _ ha))
  -- Is Causality Rel
  · exact lpo_sup_IsCausalityRel hd hne
  -- No Successors of ⊥
  · intro x hsup y α hα; refine α.property.bot _ ?_ _
    refine le_antisymm (le_of_le_of_eq ?_ hsup) bot_le
    refine DirectedOn.le_sSup (lpo_lab_directed hd x) ?_
    exact ⟨α, hα, rfl⟩
  -- Formula Domain
  · intro x; constructor
    · intro ⟨v, α, hα, hform⟩; refine ⟨α, hα, ?_⟩
      exact (α.property.form_dom x).mp ⟨v, hform⟩
    · intro ⟨α, hα, hx⟩
      obtain ⟨v, hform⟩ := (α.property.form_dom x).mpr hx
      exact ⟨v, α, hα, hform⟩
  -- Other Formula Properties
  · intro x α hα hx; constructor
    · rw [form_vars_set hd hα hx]
      simp only [Set.mem_iUnion, exists_prop, forall_exists_index, and_imp]
      intro y β hβ hy; refine ⟨β, hβ, ?_⟩
      refine (β.property.form x ?_).1 _ hy
      refine (β.property.form_dom x).mp ?_
      simp [Form.vars, Form.free] at hy
      obtain ⟨v, hv⟩ := hy
      by_cases hsat : β.form x v
      · exact ⟨v, hsat⟩
      · exact ⟨_, (not_iff.mp hv).mp hsat⟩
    · intro z a ha hxz v ⟨b, hb, hform⟩
      obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
      refine ⟨c, hc, ?_⟩
      have hx := (a.property.rel_dom hxz).1
      refine (c.property.form x (hac.nodes hx)).2 _ (le_rel hac hxz) v ?_
      exact le_form hbc v hform

theorem lpo_sup_of_directed {d : Set (Lpo l)} (h : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) :
    ∃ hv, sSup d = ⟨lpo_base_sup d, hv⟩ := by
  have hv := lpo_sup_valid h hne
  use hv; simp [sSup]
  rw [dite_cond_eq_true]; refine propext ⟨fun _ => True.intro, fun _ => hv⟩

lemma le_lpo_sup {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) {hv} :
    ∀ α ∈ d, α ≤ ⟨lpo_base_sup d, hv⟩ := by
  intro a ha; unfold lpo_base_sup; constructor
  · intro x hx; simp only [Lpo.nodes, Set.mem_iUnion, exists_prop]
    exact ⟨a, ha, hx⟩
  · intro x hx y ⟨b, hb, hr⟩
    rcases hd _ ha _ hb with ⟨c, hc, hac, hbc⟩
    rcases b.property.rel_dom hr with ⟨hyb, hxb⟩
    rw [hbc.rel _ hyb _ hxb] at hr
    exact (hac.downcl x hx y hr)
  · intro x hx y hy; simp only [Lpo.rel]; ext; refine ⟨fun hr => ⟨a, ha, hr⟩, ?_⟩
    simp only [forall_exists_index, and_imp]; intro b hb hr
    rcases hd _ ha _ hb with ⟨c, hc, hac, hbc⟩
    rcases b.property.rel_dom hr with ⟨hxb, hyb⟩
    refine (hac.rel _ hx _ hy).mpr ?_
    exact (hbc.rel _ hxb _ hyb).mp hr
  · simp [Lpo.lab]; intro x; refine DirectedOn.le_sSup ?_ ⟨a, ha, rfl⟩
    rintro ℓ₁ ⟨b, hb, hℓ₁⟩ ℓ₂ ⟨c, hc, hℓ₂⟩; simp; subst ℓ₁ ℓ₂
    rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
    exact ⟨e.lab x, ⟨e, he, rfl⟩, hbe.lab x, hce.lab x⟩
  · intro x hx; simp [Lpo.form]; ext v; refine ⟨fun hf => ⟨a, ha, hf⟩, ?_⟩
    intro ⟨b, hb, hf⟩
    rcases hd _ ha _ hb with ⟨c, hc, hac, hbc⟩
    refine (congrFun (hac.form _ hx) _).mpr ?_
    exact le_form hbc v hf
  · simp only [Lpo.nodes, Set.mem_iUnion, exists_prop, Lpo.rel, forall_exists_index, and_imp]
    intro x b hb hxb
    obtain ⟨c, hc, hac, hbc⟩ := hd _ ha _ hb
    rcases hac.succ x (hbc.nodes hxb) with hxa | ⟨z, hz, hzx⟩
    · left; exact hxa
    · right; exact ⟨z, hz, c, hc, hzx⟩

lemma lpo_sup_le {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) {a : Lpo l} {hv}
    (ha : ∀ b ∈ d, b ≤ a) : ⟨lpo_base_sup d, hv⟩ ≤ a := by
  unfold lpo_base_sup; constructor
  · simp only [Lpo.nodes, Set.iUnion_subset_iff]; intro b hb; exact (ha _ hb).nodes
  · simp only [Rel.is_down_closed, Lpo.nodes, Set.mem_iUnion, exists_prop, forall_exists_index,
      and_imp]
    intro x b hb hx y hyx; refine ⟨b, hb, ?_⟩
    exact (ha _ hb).downcl x hx y hyx
  · simp [Lpo.nodes, Lpo.rel]; intro x b hb hx y c hc hy; constructor
    · intro ⟨e, he, hr⟩
      rcases e.property.rel_dom hr with ⟨hxe, hye⟩
      exact (iff_of_eq ((ha _ he).rel _ hxe _ hye)).1 hr
    · intro hr; rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
      have hxe := hbe.nodes hx
      have hye := hce.nodes hy
      refine ⟨e, he, ?_⟩
      exact (iff_of_eq ((ha _ he).rel _ hxe _ hye)).2 hr
  · simp [Lpo.lab]; intro x; refine DirectedOn.sSup_le ?_ ?_
    · intro ℓ₁ ⟨b, hb, hl1⟩ ℓ₂ ⟨c, hc, hl2⟩; subst hl1 hl2
      rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
      exact ⟨e.lab x, ⟨e, he, rfl⟩, hbe.lab x, hce.lab x⟩
    · intro ℓ ⟨b, hb, hℓ⟩; subst hℓ; exact (ha _ hb).lab x
  · simp only [Lpo.nodes, Set.mem_iUnion, exists_prop, Lpo.form, forall_exists_index, and_imp]
    intro x b hb hx; ext v; constructor
    · intro ⟨c, hc, hf⟩; exact le_form (ha _ hc) v hf
    · intro hf; refine ⟨b, hb, ?_⟩; exact (congrFun ((ha _ hb).form _ hx) _).mpr hf
  · simp only [Lpo.nodes, Set.mem_iUnion, exists_prop, Lpo.bots, Lpo.lab, Set.mem_setOf_eq]
    intro x hx
    obtain ⟨b, hb, hlab'⟩ := lpo_directed_exists_preds hd hne (a.property.rel.fin_prec x)
    rcases (ha _ hb).succ x hx with hx' | ⟨z, hz, hzx⟩
    · left; exact ⟨b, hb, hx'⟩
    · right; refine ⟨z, ⟨⟨b, hb, hz.1⟩, ?_⟩, hzx⟩
      refine eq_bot_iff.mpr (DirectedOn.sSup_le (lpo_lab_directed hd z) ?_)
      rintro _ ⟨c, hc, rfl⟩; refine eq_bot_iff.mp ?_
      rcases hlab' z hzx with h | h
      · exfalso; exact h hz.2
      · exact h _ hc

-- Lpo is not a CompletePartialOrder, since the Lean definition of directed set does not
-- exclude empty sets
theorem lpo_sup_is_lub {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) :
    IsLUB d (sSup d) := by
  rcases lpo_sup_of_directed hd hne with ⟨hv, heq⟩; rw [heq]
  unfold lpo_base_sup; constructor
  · exact le_lpo_sup hd
  · intro α hα; exact lpo_sup_le hd hne hα
