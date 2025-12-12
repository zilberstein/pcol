import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Order

namespace Lpo
open Classical

variable {l : Type} [PartialOrder l] [OrderBot l]

noncomputable def guard_base (x : Node) (b : l) (α : Lpo l) (β : Lpo l) : Lpo_base l := {
  nodes := Set.insert x (α.nodes ∪ β.nodes)
  rel y z := α.rel y z ∨ β.rel y z ∨ (x = y ∧ z ∈ (α.nodes ∪ β.nodes))
  lab y := if x = y then b else if y ∈ α.nodes then α.lab y else β.lab y
  form y :=
    if x = y then
      Form.true
    else if y ∈ α.nodes then
      (α.form y).and (Form.literal x)
    else
      (β.form y).and (Form.literal x).not
}

lemma guard_lev {x : Node} {b : l} {α β : Lpo l} :
    (guard_base x b α β).rel.lev =
    fun y ↦ if x = y then 0 else if y ∈ α.nodes then α.rel.lev y + 1 else β.rel.lev y + 1 := by
  ext y; simp only [Rel.lev, guard_base, Set.mem_union]
  by_cases hx : x = y
  · simp only [hx, ↓reduceIte]; subst hx; sorry
  · sorry

lemma guard_rel_valid {x : Node} {b : l} {α : Lpo l} {β : Lpo l}
    (hx₁ : x ∉ α.nodes) (hx₂ : x ∉ β.nodes) (h : Disjoint α.nodes β.nodes) :
    Rel.IsCausalityRel (guard_base x b α β).rel (guard_base x b α β).nodes := by
  constructor
  -- Transitivity
  · intro y z w
    rintro (hyz | hyz | ⟨rfl, hx | hx⟩) (hzw | hzw | ⟨rfl, hw | hw⟩) <;>
      (try exfalso; exact hx₁ (α.property.rel_dom hyz).2) <;>
      (try exfalso; exact hx₂ (β.property.rel_dom hyz).2) <;>
      (try exfalso; exact hx₁ hx) <;>
      (try exfalso; exact hx₂ hx)
    · left; exact α.property.rel.trans hyz hzw
    · exfalso; exact Set.disjoint_left.mp h (α.property.rel_dom hyz).2 (β.property.rel_dom hzw).1
    · exfalso; exact Set.disjoint_left.mp h (α.property.rel_dom hzw).1 (β.property.rel_dom hyz).2
    · right; left; exact β.property.rel.trans hyz hzw
    · right; right; exact ⟨rfl, Or.inl (α.property.rel_dom hzw).2⟩
    · right; right; exact ⟨rfl, Or.inr (β.property.rel_dom hzw).2⟩
    · right; right; exact ⟨rfl, Or.inl (α.property.rel_dom hzw).2⟩
    · right; right; exact ⟨rfl, Or.inr (β.property.rel_dom hzw).2⟩
  -- Antisymmetry
  · intro y z
    rintro (hyz | hyz | ⟨rfl, hx⟩) (hzy | hzy | ⟨rfl, hy⟩)
    · exact α.property.rel.antisymm hyz hzy
    · exfalso
      exact Set.disjoint_left.mp h (α.property.rel_dom hyz).1 (β.property.rel_dom hzy).2
    · exfalso; exact hx₁ (α.property.rel_dom hyz).2
    · exfalso
      exact Set.disjoint_left.mp h (α.property.rel_dom hzy).1 (β.property.rel_dom hyz).2
    · exact β.property.rel.antisymm hyz hzy
    · exfalso; exact hx₂ (β.property.rel_dom hyz).2
    · exfalso; exact hx₁ (α.property.rel_dom hzy).2
    · exfalso; exact hx₂ (β.property.rel_dom hzy).2
    · rfl
  -- Irreflexitivity
  · rintro y (hy | hy | ⟨rfl, _ | _⟩) <;> try contradiction
    · exact α.property.rel.irrefl _ hy
    · exact β.property.rel.irrefl _ hy
  -- Finitely Preceded
  · sorry
  -- Finite Levels
  · sorry
    -- intro n; rw [guard_lev]; simp only [Set.preimage, Set.mem_singleton_iff]
    -- by_cases hn : n = 0
    -- · subst hn; refine (Set.finite_singleton x).subset ?_
    --   simp only [ite_eq_left_iff, Set.subset_singleton_iff, Set.mem_setOf_eq]; intro y hy
    --   by_cases hx : x = y
    --   · exact hx.symm
    --   · apply hy at hx; by_cases hy : y ∈ α.nodes <;>
    --       simp only [hy, ↓reduceIte, AddLeftCancelMonoid.add_eq_zero, one_ne_zero, and_false] at hx
    -- · refine (Set.Finite.union (α.property.rel.fin_lev (n - 1)) (β.property.rel.fin_lev (n - 1))).subset ?_
    --   intro y; simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_preimage, Set.mem_singleton_iff]
    --   intro hy; by_cases hx : x = y <;> simp only [hx, ↓reduceIte] at hy
    --   · exfalso; exact hn hy.symm
    --   · by_cases hy' : y ∈ α.nodes <;> simp only [hy', ↓reduceIte] at hy
    --     · left; rw [← hy, add_tsub_cancel_right]; rfl
    --     · right; rw [← hy, add_tsub_cancel_right]; rfl
  -- Single-Rooted
  · sorry
    -- use x; simp only [Rel.roots, guard_base, Set.mem_union, not_or, not_and]
    -- ext y; constructor
    -- · simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_singleton_iff, and_imp]
    --   intro hr hy; rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy | hy)
    --   · rfl
    --   · exfalso; exact ((hr x).2.2 rfl).1 hy
    --   · exfalso; exact ((hr x).2.2 rfl).2 hy
    -- · simp only [Set.mem_singleton_iff, Set.mem_inter_iff, Set.mem_setOf_eq]
    --   rintro rfl; refine ⟨fun z ↦ ⟨?_, ?_, ?_⟩, ?_⟩
    --   · intro hc; exact hx₁ (α.property.rel_dom hc).2
    --   · intro hc; exact hx₂ (β.property.rel_dom hc).2
    --   · rintro rfl; exact ⟨hx₁, hx₂⟩
    --   · exact Set.mem_insert _ _

noncomputable def guard (x : Node) (b : l) (α : Lpo l) (β : Lpo l)
    (hx₁ : x ∉ α.nodes) (hx₂ : x ∉ β.nodes) (h : Disjoint α.nodes β.nodes)
    (hb : b ≠ ⊥) : Lpo l :=
  Subtype.mk (guard_base x b α β) (by
    constructor <;> simp only [guard_base, nodes, rel, Set.mem_union]
    · rintro y z (hr | hr | ⟨rfl, hz | hz⟩)
      · rcases α.property.rel_dom hr with ⟨hy, hz⟩
        exact ⟨Set.mem_insert_of_mem _ (Or.inl hy), Set.mem_insert_of_mem _ (Or.inl hz)⟩
      · rcases β.property.rel_dom hr with ⟨hy, hz⟩
        exact ⟨Set.mem_insert_of_mem _ (Or.inr hy), Set.mem_insert_of_mem _ (Or.inr hz)⟩
      · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ (Or.inl hz)⟩
      · exact ⟨Set.mem_insert _ _, Set.mem_insert_of_mem _ (Or.inr hz)⟩
    · intro y hy
      apply Set.mem_insert_iff.mpr.mt at hy; simp only [Set.mem_union, not_or] at hy
      rcases hy with ⟨hneq, hyα, hyβ⟩
      simp only [Ne.symm hneq, ↓reduceIte, hyα]
      exact β.property.lab_dom _ hyβ
    · exact guard_rel_valid hx₁ hx₂ h (b := b)
    · rintro y hlab z (hyz | hyz | ⟨rfl, _⟩)
      · have hy := (α.property.rel_dom hyz).1
        have hx : x ≠ y := by rintro rfl; exact hx₁ hy
        simp only [hx, ↓reduceIte, hy] at hlab
        exact α.property.bot _ hlab _ hyz
      · have hy := (β.property.rel_dom hyz).1
        have hx : x ≠ y := by rintro rfl; exact hx₂ hy
        have hy' : y ∉ α.val.nodes := Set.disjoint_right.mp h hy
        simp only [hx, ↓reduceIte, hy'] at hlab
        exact β.property.bot _ hlab _ hyz
      · simp only [↓reduceIte] at hlab; exact hb hlab
    · intro y; by_cases hx : x = y <;> simp only [hx, ↓reduceIte]
      · refine ⟨fun _ ↦ Set.mem_insert _ _, fun _ ↦ ⟨∅, ?_⟩⟩; simp only [Form.true]
      · by_cases hy : y ∈ α.val.nodes <;> simp only [hy, ↓reduceIte]
        · refine ⟨fun _ ↦ Set.mem_insert_of_mem _ (Or.inl hy), fun _ ↦ ?_⟩
          obtain ⟨v, hform⟩ := (α.property.form_dom y).mpr hy
          use (Set.insert x v); simp only [Form.and, Form.literal]
          refine ⟨?_, Set.mem_insert _ _⟩
          sorry
        · sorry
    · intro y hy; sorry
 )

 lemma guard_monotone {x : Node} {b b' : l} {α α' β β' : Lpo l}
    (hx₁ : x ∉ α'.nodes) (hx₂ : x ∉ β'.nodes) (hd : Disjoint α'.nodes β'.nodes)
    (hb : b ≠ ⊥) (hle₁ : α ≤ α') (hle₂ : β ≤ β') (hleb : b ≤ b') :
    guard x b α β
      (fun hx ↦ hx₁ (hle₁.nodes hx))
      (fun hx ↦ hx₂ (hle₂.nodes hx))
      (hd.mono hle₁.nodes hle₂.nodes) hb ≤
    guard x b' α' β' hx₁ hx₂ hd (ne_bot_of_le_ne_bot hb hleb) := by
  constructor <;> simp only [guard, guard_base, nodes, rel, form, lab, Set.mem_union]
  · exact Set.insert_subset_insert (Set.union_subset_union hle₁.nodes hle₂.nodes)
  · rintro y hy z (hz | hz | ⟨rfl, hz | hz⟩) <;>
    rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy | hy) <;>
    try (exact Set.mem_insert _ _)
    · exfalso; exact hx₁ (α'.property.rel_dom hz).2
    · exact Set.mem_insert_of_mem _ (Set.mem_union_left _ (hle₁.downcl _ hy _ hz))
    · exfalso; refine Set.disjoint_left.mp hd ?_ (hle₂.nodes hy)
      exact (α'.property.rel_dom hz).2
    · exfalso; exact hx₂ (β'.property.rel_dom hz).2
    · exfalso; refine Set.disjoint_right.mp hd ?_ (hle₁.nodes hy)
      exact (β'.property.rel_dom hz).2
    · exact Set.mem_insert_of_mem _ (Set.mem_union_right _ (hle₂.downcl _ hy _ hz))
  · intro y hy z hz
    have hrel₁ {γ γ' : Lpo l} (hle : γ ≤ γ') {u v : Node}
        (h : u ∉ γ'.nodes) : γ.rel u v = γ'.rel u v := by
      ext; constructor <;> intro hc <;> exfalso
      · exact h (hle.nodes (γ.property.rel_dom hc).1)
      · exact h (γ'.property.rel_dom hc).1
    have hrel₂ {γ γ' : Lpo l} (hle : γ ≤ γ') {u v : Node}
        (h : v ∉ γ'.nodes) : γ.rel u v = γ'.rel u v := by
      ext; constructor <;> intro hc <;> exfalso
      · exact h (hle.nodes (γ.property.rel_dom hc).2)
      · exact h (γ'.property.rel_dom hc).2
    have hx₁' := (fun hx ↦ hx₁ (hle₁.nodes hx))
    have hx₂' := (fun hx ↦ hx₂ (hle₂.nodes hx))
    rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy' | hy') <;>
    rcases Set.eq_or_mem_of_mem_insert hz with (rfl | hz | hz) <;>
    refine congrArg₂ _ ?_ (congrArg₂ _ ?_ ?_) <;>
    (try ext; constructor <;> rintro ⟨rfl, _⟩ <;> exfalso <;>
        exact hx₁ (hle₁.nodes hy')) <;>
    (try ext; constructor <;> rintro ⟨rfl, _⟩ <;> exfalso <;>
        exact hx₂ (hle₂.nodes hy')) <;>
    (try refine hrel₁ hle₁ ?_; assumption) <;>
    (try refine hrel₂ hle₁ ?_; assumption) <;>
    (try refine hrel₁ hle₂ ?_; assumption) <;>
    (try refine hrel₂ hle₂ ?_; assumption)
    · refine congrArg₂ _ rfl (congrArg₂ _ ?_ ?_)
      · ext; exact ⟨fun h ↦ False.elim (hx₁ (hle₁.nodes h)),
                     fun h ↦ False.elim (hx₁ h)⟩
      · ext; exact ⟨fun h ↦ False.elim (hx₂ (hle₂.nodes h)),
                     fun h ↦ False.elim (hx₂ h)⟩
    · refine congrArg₂ _ rfl (congrArg₂ _ ?_ ?_)
      · ext; exact ⟨fun _ ↦ hle₁.nodes hz, fun _ ↦ hz⟩
      · ext; constructor
        · intro hc; exfalso
          exact Set.disjoint_left.mp hd (hle₁.nodes hz) (hle₂.nodes hc)
        · intro hc; exfalso
          exact Set.disjoint_left.mp hd (hle₁.nodes hz) hc
    · refine congrArg₂ _ rfl (congrArg₂ _ ?_ ?_) <;> ext <;> constructor <;>
        intro h
      · exact hle₁.nodes h
      · exfalso; exact Set.disjoint_left.mp hd h (hle₂.nodes hz)
      · exact hle₂.nodes h
      · exact hz
    · exact hle₁.rel _ hy' _ hz
    · exact hrel₁ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hy'))
    · exact hrel₂ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hz))
    · exact hrel₁ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hy'))
    · exact hrel₁ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hy'))
    · exact hrel₂ hle₂ (Set.disjoint_left.mp hd (hle₁.nodes hz))
    · exact hrel₁ hle₁ (Set.disjoint_right.mp hd (hle₂.nodes hy'))
    · exact hle₂.rel _ hy' _ hz
  · intro y; by_cases hx : x = y <;> simp only [hx, ↓reduceIte]
    · exact hleb
    · by_cases hy : y ∈ α'.val.nodes <;> simp only [hy, ↓reduceIte]
      · by_cases hy' : y ∈ α.val.nodes <;> simp only [hy', ↓reduceIte]
        · exact hle₁.lab y
        · refine le_of_eq_of_le ?_ bot_le
          refine β.property.lab_dom _ fun hx ↦ Set.disjoint_left.mp hd hy (hle₂.nodes hx)
      · have hy' : y ∉ α.val.nodes := fun hy' ↦ hy (hle₁.nodes hy')
        simp only [hy', ↓reduceIte]; exact hle₂.lab y
  · intro y hy; rcases Set.eq_or_mem_of_mem_insert hy with (rfl | hy | hy)
    · simp only [↓reduceIte]
    · have hx : x ≠ y := by rintro rfl; exact hx₁ (hle₁.nodes hy)
      have hy' : y ∈ α'.val.nodes := hle₁.nodes hy
      simp only [↓reduceIte, hx, hy, hy']
      exact congrArg₂ _ (hle₁.form _ hy) rfl
    · have hx : x ≠ y := by rintro rfl; exact hx₂ (hle₂.nodes hy)
      have hyβ' : y ∈ β'.val.nodes := hle₂.nodes hy
      have hyα' : y ∉ α'.val.nodes := Set.disjoint_right.mp hd hyβ'
      have hyα : y ∉ α.val.nodes := fun h ↦ hyα' (hle₁.nodes h)
      simp only [↓reduceIte, hx, hyα, hyα']
      exact congrArg₂ _ (hle₂.form _ hy) rfl
  · intro y hy; sorry

end Lpo
