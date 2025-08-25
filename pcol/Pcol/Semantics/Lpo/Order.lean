import Mathlib
import Pcol.Semantics.Lpo.Basic

def is_down_closed (ord : Rel Node Node) (X : Set Node) : Prop :=
  ∀ x ∈ X, ∀ y, ord y x → y ∈ X

def up_closure (ord : Rel Node Node) (X : Set Node) : Set Node :=
  { x | ∃ y ∈ X, ord y x }

structure LE_Lpo {l : Type} [LE l] [Bot l] (a b : Lpo l) : Prop where
  nodes : a.nodes ⊆ b.nodes
  downcl : is_down_closed b.rel a.nodes
  rel : ∀ x ∈ a.nodes, ∀ y ∈ a.nodes, a.rel x y = b.rel x y
  lab : ∀ x, a.lab x ≤ b.lab x
  form : ∀ x ∈ a.nodes, a.form x = b.form x
  succ : ∀ x ∈ a.nodes, a.rel.succ x = b.rel.succ x \ up_closure b.rel a.bots

instance {l : Type} [LE l] [Bot l] : LE (Lpo l) where
  le a b := LE_Lpo a b

lemma up_closure_same_empty {l : Type} [Bot l] {a : Lpo l} :
  up_closure a.rel a.bots = ∅ := by { sorry }
--     match a with
--     | ⟨a', ⟨_, hbot, _⟩⟩ =>
--       unfold up_closure; ext x; constructor
--       · rintro ⟨y, hybot, hrel⟩
--         have h := hbot y hybot
--         rw [castNode_idem] at hrel
--         sorry
--         --This proof sets a bit tricky, and I think it depends on Well-foundedness of rel
--       · intro hc; contradiction
-- }

instance {l : Type} [Preorder l] [Bot l] : Preorder (Lpo l) where
  le_refl a := by {
    constructor <;> try simp
    · intro x hx y hr; exact (a.property.rel_dom hr).1
    · intro x hx; rw [up_closure_same_empty]; simp
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
    · intro x hx; sorry -- Need some lemmas about succ
  }

instance {l : Type} [PartialOrder l] [Bot l] : PartialOrder (Lpo l) where
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
      · sorry -- This is easy, but I don't feel like doing it right now
  }

def lpo_base_sup {l : Type} [SupSet l] [Bot l] (s : Set (Lpo l)) : Lpo_base l := {
  nodes := ⋃ a ∈ s, a.nodes
  rel x y := ∃ a ∈ s, a.rel x y
  lab x := sSup { l | ∃ a ∈ s, l = a.lab x }
  form x v := ∃ a ∈ s, a.form x v
}

instance {l : Type} [Bot l] : Inhabited (Lpo l) where
  default := Lpo.singleton default ⊥

noncomputable instance {l : Type} [SupSet l] [Bot l] : SupSet (Lpo l) where
  sSup s : Lpo l := by {
    by_cases h : is_valid_lpo (lpo_base_sup s)
    · exact ⟨lpo_base_sup s, h⟩
    · exact default
  }

theorem lpo_sup_of_directed {l : Type} [SupSet l] [LE l] [Bot l] {d : Set (Lpo l)}
  (h : DirectedOn (· ≤ ·)  d) :
  ∃ hv, sSup d = ⟨lpo_base_sup d, hv⟩ := by {
  have hv : is_valid_lpo (lpo_base_sup d) := by {
    unfold lpo_base_sup; constructor <;> try simp
    · intro x y a ha hrel
      rcases a.property.rel_dom hrel with ⟨hx, hy⟩
      exact ⟨⟨a, ha, hx⟩, ⟨a, ha, hy⟩⟩
    · intro x hx; sorry
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
      · sorry
      · sorry
      · sorry
    · sorry
    · sorry
    · intro x a hx; sorry
  }
  use hv; simp [sSup]
  rw [dite_cond_eq_true]; refine propext ⟨fun _ => trivial, fun _ => hv⟩
}

-- Lpo is not a CompletePartialOrder, since the Lean definition of directed set does not
-- exclude empty sets
theorem lpo_sup_is_lub {l : Type} [Bot l] [CompletePartialOrder l] {d : Set (Lpo l)}
  (hd : DirectedOn (· ≤ ·)  d) (hne : d.Nonempty) : IsLUB d (sSup d) := by {
  rcases lpo_sup_of_directed hd with ⟨hv, heq⟩; rw [heq]
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
      -- easy, but I'll do it later
      sorry
    · simp [Lpo.lab]; intro x; refine DirectedOn.le_sSup ?_ ⟨a, ha, rfl⟩
      rintro ℓ₁ ⟨b, hb, hℓ₁⟩ ℓ₂ ⟨c, hc, hℓ₂⟩; simp; subst ℓ₁ ℓ₂
      rcases hd _ hb _ hc with ⟨e, he, hbe, hce⟩
      exact ⟨e.lab x, ⟨e, he, rfl⟩, hbe.lab x, hce.lab x⟩
    · intro x hx; simp [Lpo.form]; ext v; refine ⟨fun hf => ⟨a, ha, hf⟩, ?_⟩
      intro ⟨b, hb, hf⟩
      rcases hd _ ha _ hb with ⟨c, hc, hac, hbc⟩
      -- need to do the rewriting with coercions, annoying
      sorry
    · simp [Lpo.rel]; intro h ha; sorry
  · simp [lowerBounds, upperBounds]; intro a ha; constructor
    · simp [Lpo.nodes]; intro b hb; exact (ha hb).nodes
    · simp [is_down_closed, Lpo.nodes]; intro x b hb hx y hyx; refine ⟨b, hb, ?_⟩
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
    · simp [Lpo.nodes, Lpo.form]
      intro x b hb hx; sorry
    · sorry
}
