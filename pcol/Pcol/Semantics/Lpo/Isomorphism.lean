import Mathlib
import Pcol.Semantics.Lpo.Basic

namespace Lpo

noncomputable def permute {l : Type} [Bot l] (a : Lpo l)
  (f : Node → Node) (hf : Function.Bijective f) : Lpo l :=
  let finv := f.surjInv hf.2
  Subtype.mk {
    nodes := f '' a.nodes
    rel x y := a.rel (finv x) (finv y)
    lab x := a.lab (finv x)
    form x v := a.form (finv x) (f '' v)
  } (by {
    have hinv {a : Lpo l} {x} (hx : finv x ∈ a.nodes) : ∃ y ∈ a.nodes, f y = x :=
      ⟨f.surjInv hf.2 x, hx, Function.surjInv_eq hf.2 _⟩
    constructor <;> try simp
    · intro x y hr
      rcases a.property.rel_dom hr with ⟨hx, hy⟩
      exact ⟨hinv hx, hinv hy⟩
    · intro x hx
      have hx' : finv x ∉ a.nodes := fun h =>
        hx _ h (Function.surjInv_eq hf.2 _)
      exact a.property.lab_dom _ hx'
    · constructor
      · intro _ _ _ hxy hyz; exact a.property.rel.trans hxy hyz
      · intro _ _ hxy hyx
        have hi := Function.injective_surjInv hf.2
        exact hi.eq_iff.1 (a.property.rel.antisymm hxy hyx)
      · intro _ hx; exact a.property.rel.irrefl _ hx
      · sorry --constructor; intro x; constructor; intro y hr
      · sorry
      · rcases a.property.rel.single_rooted with ⟨x, hx⟩
        use finv x; unfold Rel.roots; simp; sorry
    · intro _ hx _; exact a.property.bot _ hx _
    · intro x; constructor
      · intro ⟨_, h⟩; exact hinv ((a.property.form_dom _).1 ⟨_, h⟩)
      · intro ⟨y, hy, hxy⟩; rw [← hxy]
        unfold finv; rw [Function.leftInverse_surjInv hf y]
        rcases (a.property.form_dom _).2 hy with ⟨v, h⟩
        use (finv '' v); simp; rw [← Set.image_comp]
        have heq : f ∘ finv = id := by ext _; exact Function.surjInv_eq hf.2 _
        rw [heq, Set.image_id]; exact h
    · sorry
--        · simp [Form.vars]; intro y hy
  })

 def IsIsomorphic {l : Type} [Bot l] (a b : Lpo l) : Prop :=
  ∃ f hf, a.permute f hf = b

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by {
  constructor
  -- Reflexivity
  · intro a; refine ⟨id, Function.bijective_id, ?_⟩; unfold permute; apply lpo_eq_iff.2
    have h (z : Node) : Function.surjInv Function.bijective_id.2 z = z := by {
      apply Function.injective_id.eq_iff.1; rw [Function.surjInv_eq Function.bijective_id.2 z]; rfl
    }
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp [Lpo.nodes]
    · simp [Lpo.rel]; ext x y; rw [h x, h y]
    · simp [Lpo.lab]; ext x; rw [h x]
    · simp [Lpo.form]; ext1 x ; rw [h x]
  -- Symmetry
  · intro a b ⟨f, hf, hb⟩
    refine ⟨Function.surjInv hf.2, ⟨Function.injective_surjInv hf.2, ?_⟩, ?_⟩
    · intro x; use f x; exact Function.leftInverse_surjInv hf x
    · rw [← hb]; unfold Lpo.permute; apply lpo_eq_iff.2; refine ⟨?_, ?_, ?_, ?_⟩
      · simp [nodes]; rw [← Set.image_comp]
        have heq : Function.surjInv hf.2 ∘ f = id := by ext x; exact Function.leftInverse_surjInv hf x
        rw [heq, Set.image_id]
      · simp [Lpo.rel]; sorry
      · sorry
      · sorry
  -- Transitivity
  · intro a b c ⟨f, hf, hab⟩ ⟨g, hg, hbc⟩
    refine ⟨g ∘ f, Function.Bijective.comp hg hf, ?_⟩
    apply lpo_eq_iff.2
    rcases lpo_eq_iff.1 hab with ⟨hna, hra, hla, hfa⟩
    rcases lpo_eq_iff.1 hbc with ⟨hnb, hrb, hlb, hfb⟩
    unfold permute at *; simp [Lpo.nodes, Lpo.rel, Lpo.form, Lpo.lab] at *
    refine ⟨?_, ?_, ?_, ?_⟩
    · have heq : (fun a ↦ g (f a)) = g ∘ f := rfl
      rw [heq, Set.image_comp, hna]; exact hnb
    · sorry
    · sorry
    · sorry
}

instance instSetoid {l : Type} [Bot l] : Setoid (Lpo l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

end Lpo
