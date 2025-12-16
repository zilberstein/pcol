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

lemma lpo_directed_lev_eq {d : Set (Lpo l)} (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty)
    (x : Node) : ∃ n : ℕ, ∀ α ∈ d, x ∈ α.nodes → α.rel.lev x = n := sorry

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
      have h' : ∀ x ∈ X, ∃ α ∈ d, x ∈ α.nodes ∧ (α.lab x ≠ ⊥ ∨ ∀ β ∈ d, β.lab x = ⊥) := by
        unfold X; intro x ⟨s, hs, hx⟩; by_cases hlab : ∃ β ∈ d, β.lab x ≠ ⊥
        · obtain ⟨β, hβ, hlab⟩ := hlab; refine ⟨β, hβ, ?_, Or.inl hlab⟩
          exact Set.not_not_mem.mp ((β.property.lab_dom x).mt hlab)
        · simp only [ne_eq, not_exists, not_and, not_not] at hlab
          rcases Set.mem_range.mp hs with ⟨k, rfl⟩
          have h := (hf k.val k.isLt).2.1 hx
          simp only [Set.mem_iUnion, exists_prop] at h
          rcases h with ⟨α ,hα, hx⟩
          exact ⟨α , hα, hx, Or.inr hlab⟩
      choose g hg using h'
      let A : Set (Lpo l):= (fun x ↦ g x.val x.property) '' (Set.univ : Set ↑X)
      have hfin' : A.Finite := (Set.finite_univ_iff.mpr hfin).image _
      have hsub : A ⊆ d := by
        intro α hα; simp [A] at hα
        rcases hα with ⟨x, hx, rfl⟩; exact (hg x hx).1
      obtain ⟨α, hα, hub⟩ := directed_finite_upper_bound h hne hsub hfin'
      refine ⟨{ x ∈ α.nodes | α.rel.lev x = n + 1 }, ?_, ?_, ?_⟩
      · exact α.property.rel.fin_lev _
      · intro x ⟨hx, _⟩; simp only [Set.mem_iUnion, exists_prop]
        exact ⟨α, hα, hx⟩
      · intro β hβ x ⟨hx, hlev⟩; constructor
        · sorry
        · sorry

theorem lpo_sup_of_directed {d : Set (Lpo l)} (h : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) :
  ∃ hv, sSup d = ⟨lpo_base_sup d, hv⟩ := by {
  have hv : is_valid_lpo (lpo_base_sup d) := by {
    unfold lpo_base_sup; constructor <;> try simp
    · intro x y a ha hrel
      rcases a.property.rel_dom hrel with ⟨hx, hy⟩
      exact ⟨⟨a, ha, hx⟩, ⟨a, ha, hy⟩⟩
    · intro x hx; refine bot_unique (DirectedOn.sSup_le ?_ ?_)
      · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        refine ⟨⊥, ⟨a, ha, ?_⟩, ?_, ?_⟩
        · exact (a.property.lab_dom _ (hx _ ha)).symm
        · exact le_of_eq (a.property.lab_dom _ (hx _ ha))
        · exact le_of_eq (b.property.lab_dom _ (hx _ hb))
      · rintro _ ⟨a, ha, rfl⟩; exact le_of_eq (a.property.lab_dom _ (hx _ ha))
    · constructor
      · rintro x y z ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
        rcases h a ha b hb with ⟨c, hc, hac, hbc⟩
        refine ⟨c, hc, ?_⟩
        refine c.property.rel.trans ?_ ?_ (y := y)
        · have hxy := a.property.rel_dom har
          rw [hac.rel _ hxy.1 _ hxy.2] at har
          exact har
        · have hyz := b.property.rel_dom hbr
          rw [hbc.rel _ hyz.1 _ hyz.2] at hbr
          exact hbr
      · intro x y ⟨a, ha, har⟩ ⟨b, hb, hbr⟩
        rcases h a ha b hb with ⟨c, hc, hac, hbc⟩
        have hxy := a.property.rel_dom har
        rw [hac.rel _ hxy.1 _ hxy.2] at har
        have hyx := b.property.rel_dom hbr
        rw [hbc.rel _ hyx.1 _ hyx.2] at hbr
        exact c.property.rel.antisymm har hbr
      · intro x ⟨a, _, hr⟩; exact a.property.rel.irrefl _ hr
      · intro x; by_cases hx : ∃ a ∈ d, x ∈ a.nodes
        · rcases hx with ⟨a, ha, hx⟩; refine (congrArg _ ?_).mp (a.property.rel.fin_prec x)
          ext y; constructor
          · intro hyx; exact ⟨a, ha, hyx⟩
          · intro ⟨b, hb, hyx⟩; obtain ⟨c, hc, hac, hbc⟩ := h _ ha _ hb
            obtain ⟨hby, hbx⟩ := b.property.rel_dom hyx
            rw [hbc.rel _ hby _ hbx] at hyx
            refine (hac.rel _ ?_ _ hx).mpr hyx
            exact hac.downcl _ hx _ hyx
        · refine (congrArg _ ?_).mp Set.finite_empty; ext y; constructor
          · rintro ⟨⟩
          · intro ⟨a, ha, hyx⟩; exfalso; refine hx ⟨a, ha, ?_⟩
            exact (a.property.rel_dom hyx).2
      · intro n; obtain ⟨X, hfin, _, hub⟩ := lpo_directed_fin_lev h hne n
        refine hfin.subset ?_; intro x ⟨hx, hlev⟩
        simp only [Set.mem_iUnion, exists_prop] at hx
        rcases hx with ⟨α, hα, hx⟩; refine hub α hα ⟨hx, ?_ ⟩
        obtain ⟨k, hk⟩ := lpo_directed_lev_eq h hne x
        sorry
      · rcases hne with ⟨a, ha⟩; rcases a.property.rel.single_rooted with ⟨x, hx, hroot⟩; use x
        simp only [Set.mem_iUnion, exists_prop, ne_eq, forall_exists_index, and_imp]
        refine ⟨⟨a, ha, hx⟩, ?_⟩
        intro y b hb hy hneq; obtain ⟨c, hc, hac, hbc⟩ := h _ ha _ hb
        obtain ⟨z, hz, hroot'⟩ := c.property.rel.single_rooted; by_cases heq : z = x
        · subst heq; exact ⟨c, hc, hroot' y (hbc.nodes hy) hneq⟩
        · exfalso; have hzx := hroot' x (hac.nodes hx) heq
          refine heq (c.property.rel.antisymm hzx ?_)
          have hza := hac.downcl _ hx _ hzx
          exact (hac.rel _ hx _ hza).mp (hroot _ hza (Ne.symm heq))
    · sorry
    · sorry
    · intro x a hx; sorry
  }
  use hv; simp [sSup]
  rw [dite_cond_eq_true]; refine propext ⟨fun _ => trivial, fun _ => hv⟩
}

-- Lpo is not a CompletePartialOrder, since the Lean definition of directed set does not
-- exclude empty sets
theorem lpo_sup_is_lub {d : Set (Lpo l)}
  (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) : IsLUB d (sSup d) := by {
  rcases lpo_sup_of_directed hd hne with ⟨hv, heq⟩; rw [heq]
  unfold lpo_base_sup; constructor <;> try simp
  · unfold upperBounds; intro a ha; constructor <;> try simp
    · unfold Lpo.nodes; intro x hx; simp; use a
    · intro x hx y ⟨b, hb, hr⟩
      rcases hd _ ha _ hb with ⟨c, hc, hac, hbc⟩
      rcases b.property.rel_dom hr with ⟨hyb, hxb⟩
      rw [hbc.rel _ hyb _ hxb] at hr
      exact (hac.downcl x hx y hr)
    · intro x hx y hy; refine ⟨fun hr => ⟨a, ha, hr⟩, ?_⟩
      simp [Lpo.rel]; intro b hb hr
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
  · simp [lowerBounds, upperBounds]; intro a ha; constructor
    · simp [Lpo.nodes]; intro b hb; exact (ha hb).nodes
    · simp [Rel.is_down_closed, Lpo.nodes]; intro x b hb hx y hyx; refine ⟨b, hb, ?_⟩
      exact (ha hb).downcl x hx y hyx
    · simp [Lpo.nodes, Lpo.rel]; intro x b hb hx y c hc hy; constructor
      · intro ⟨e, he, hr⟩
        rcases e.property.rel_dom hr with ⟨hxe, hye⟩
        exact (iff_of_eq ((ha he).rel _ hxe _ hye)).1 hr
      · intro hr; rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
        have hxe := hbe.nodes hx
        have hye := hce.nodes hy
        refine ⟨e, he, ?_⟩
        exact (iff_of_eq ((ha he).rel _ hxe _ hye)).2 hr
    · simp [Lpo.lab]; intro x; refine DirectedOn.sSup_le ?_ ?_
      · intro ℓ₁ ⟨b, hb, hl1⟩ ℓ₂ ⟨c, hc, hl2⟩; subst hl1 hl2
        rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
        exact ⟨e.lab x, ⟨e, he, rfl⟩, hbe.lab x, hce.lab x⟩
      · intro ℓ ⟨b, hb, hℓ⟩; subst hℓ; exact (ha hb).lab x
    · simp only [Lpo.nodes, Set.mem_iUnion, exists_prop, Lpo.form, forall_exists_index, and_imp]
      intro x b hb hx; ext v; constructor
      · intro ⟨c, hc, hf⟩; exact le_form (ha hc) v hf
      · intro hf; refine ⟨b, hb, ?_⟩; exact (congrFun ((ha hb).form _ hx) _).mpr hf
    · simp only [Lpo.nodes, Set.mem_iUnion, exists_prop, Lpo.bots, Lpo.lab, Set.mem_setOf_eq]
      intro x hx; refine Classical.or_iff_not_imp_left.mpr ?_
      simp only [not_exists, not_and]
      intro h; sorry
}
