import Mathlib
import Pcol.Semantics.Lpo.Basic

namespace Lpo

noncomputable def permute {l : Type} [Bot l] (a : Lpo l)
  (e : Node ≃ Node) : Lpo l :=
  Subtype.mk {
    nodes := e '' a.nodes
    rel x y := a.rel (e.symm x) (e.symm y)
    lab x := a.lab (e.symm x)
    form x v := a.form (e.symm x) (e '' v)
  } (by {
    -- have hinv {a : Lpo l} {x} (hx : finv x ∈ a.nodes) : ∃ y ∈ a.nodes, f y = x :=
    --   ⟨f.surjInv hf.2 x, hx, Function.surjInv_eq hf.2 _⟩
    constructor <;> try simp
    · intro _ _ hr; exact a.property.rel_dom hr
    · intro _ hx; exact a.property.lab_dom _ hx
    · constructor
      · intro _ _ _ hxy hyz; exact a.property.rel.trans hxy hyz
      · intro _ _ hxy hyx; exact Equiv.injective _ (a.property.rel.antisymm hxy hyx)
      · intro _ hx; exact a.property.rel.irrefl _ hx
      · sorry --constructor; intro x; constructor; intro y hr
      · sorry
      · rcases a.property.rel.single_rooted with ⟨x, hx⟩
        sorry -- use e.symm x; unfold Rel.roots; simp; sorry
    · sorry -- intro _ hx _; exact a.property.bot _ hx _
    · sorry --intro x; constructor
      -- · intro ⟨_, h⟩; exact hinv ((a.property.form_dom _).1 ⟨_, h⟩)
      -- · intro ⟨y, hy, hxy⟩; rw [← hxy]
      --   unfold finv; rw [Function.leftInverse_surjInv hf y]
      --   rcases (a.property.form_dom _).2 hy with ⟨v, h⟩
      --   use (finv '' v); simp; rw [← Set.image_comp]
      --   have heq : f ∘ finv = id := by ext _; exact Function.surjInv_eq hf.2 _
      --   rw [heq, Set.image_id]; exact h
    · sorry
--        · simp [Form.vars]; intro y hy
  })

 def IsIsomorphic {l : Type} [Bot l] (a b : Lpo l) : Prop :=
    ∃ e, a.permute e = b

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by {
  constructor
  -- Reflexivity
  · intro a; refine ⟨Equiv.refl _, ?_⟩; unfold permute; apply lpo_eq_iff.2
    -- have h (z : Node) : Function.surjInv Function.bijective_id.2 z = z := by {
    --   apply Function.injective_id.eq_iff.1; rw [Function.surjInv_eq Function.bijective_id.2 z]; rfl
    -- }
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Lpo.nodes]
    · simp [Lpo.rel] --; ext x y; refine ⟨fun ⟨_, _, h⟩ => h, fun h => ?_⟩
--      rcases a.property.rel_dom h with ⟨hx, hy⟩; exact ⟨hy, hx, h⟩
    · simp [Lpo.lab] --; ext x; by_cases h : x ∈ a.nodes <;> simp [h]
--      exact Eq.symm (a.property.lab_dom x h)
    · simp [Lpo.form] --; ext1 x ; sorry -- rw [h x]
  -- Symmetry
  · intro a b ⟨e, hb⟩
    refine ⟨e.symm, ?_⟩
--    · intro x; use f x; exact Function.leftInverse_surjInv hf x
    · unfold Lpo.permute at *;
      rcases lpo_eq_iff.1 hb with ⟨_, hrel, hlab, hfo⟩;
--      simp [Lpo.nodes, Lpo.rel, Lpo.form, Lpo.lab] at *
      apply lpo_eq_iff.2; refine ⟨?_, ?_, ?_, ?_⟩
      · simp [nodes]; sorry
      · simp [Lpo.rel]; ext x y; constructor
        · sorry
          -- intro ⟨hx, hy, hb⟩; simp [Lpo.rel] at hrel; rw [← hrel] at hb
          -- simp at hb; exact hb
        · sorry
          -- intro ha; simp [Lpo.rel] at hrel
          -- have hxy := a.property.rel_dom ha
          -- refine ⟨hxy.1, hxy.2, ?_⟩; rw [← hrel]; simp; exact ha
      · sorry
      · sorry
  -- Transitivity
  · intro a b c ⟨e₁, hab⟩ ⟨e₂, hbc⟩
    refine ⟨e₁.trans e₂, ?_⟩
    apply lpo_eq_iff.2
    rcases lpo_eq_iff.1 hab with ⟨hna, hra, hla, hfa⟩
    rcases lpo_eq_iff.1 hbc with ⟨hnb, hrb, hlb, hfb⟩
    unfold permute at *; simp [Lpo.nodes, Lpo.rel, Lpo.form, Lpo.lab] at *
    refine ⟨?_, ?_, ?_⟩
    · sorry
    · sorry
    · sorry
}

instance instSetoid {l : Type} [Bot l] : Setoid (Lpo l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

end Lpo
