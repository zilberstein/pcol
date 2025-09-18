import Mathlib
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order

namespace Lpo

noncomputable def permute {l : Type} [Bot l] (a : Lpo l) (e : Equiv.Perm Node) : Lpo l :=
  Subtype.mk {
    nodes := e '' a.nodes
    rel x y := a.rel (e.symm x) (e.symm y)
    lab x := a.lab (e.symm x)
    form x v := a.form (e.symm x) (e.symm '' v)
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

lemma permute_refl {l : Type} [Bot l] (a : Lpo l) : a.permute (Equiv.refl Node) = a := by
  unfold permute; ext1 <;> simp [Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]

lemma permute_trans {l : Type} [Bot l] {a : Lpo l} {e₁ e₂ : Equiv.Perm Node} :
    (a.permute e₁).permute e₂ = a.permute (e₁.trans e₂) := by
  unfold permute; ext1
  · simp [Lpo.nodes, Set.image]
  · simp [Lpo.rel]
  · simp [Lpo.lab]
  · ext x v; simp [Lpo.form, Set.image]

lemma permute_injective {l : Type} [Bot l] (e : Equiv.Perm Node) :
    Function.Injective (fun a : Lpo l ↦ a.permute e) := by
  intros a b h;
  apply congr_arg Subtype.val at h; simp [permute] at h
  rcases h with ⟨hnodes, hrel, hlab, hform⟩
  have hn x : x = e.symm (e x) := by simp
  ext1
  · exact hnodes
  · ext x y; rw [hn x, hn y, congrFun₂ hrel]
  · ext x; rw [hn x, congrFun hlab]
  · ext x v
    have hv : v = e.symm '' (e '' v) := by simp
    rw [hn x, hv, congrFun₂ hform]

lemma permute_symm {l : Type} [Bot l] {a b : Lpo l} {e : Equiv.Perm Node} :
    a.permute e = b ↔ a = b.permute e.symm := by
  constructor
  · intro heq; rw [← heq, permute_trans, Equiv.self_trans_symm, permute_refl]
  · intro heq; rw [heq, permute_trans, Equiv.symm_trans_self, permute_refl]

def IsIsomorphic {l : Type} [Bot l] (a b : Lpo l) : Prop :=
    ∃ e, a.permute e = b

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by
  constructor
  -- Reflexivity
  · intro a; exact ⟨Equiv.refl _, permute_refl a⟩
  -- Symmetry
  · intro a b ⟨e, hb⟩; exact ⟨e.symm, (permute_symm.mp hb).symm⟩
  -- Transitivity
  · intro a b c ⟨e₁, hab⟩ ⟨e₂, hbc⟩; subst hab hbc
    exact ⟨e₁.trans e₂, permute_trans.symm⟩

instance instSetoid {l : Type} [Bot l] : Setoid (Lpo l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

lemma permute_le {l : Type} [Bot l] [LE l] {a b : Lpo l} {e : Equiv.Perm Node}
    (h : a ≤ b) : a.permute e ≤ b.permute e := by
  unfold permute; constructor
  · simp [Lpo.nodes]; exact h.nodes
  · simp [Lpo.rel, Lpo.nodes]; rintro _ ⟨x, hx, hx'⟩ y hy; subst hx'; simp at hy
    refine ⟨e.symm y, h.downcl _ hx _ hy, ?_⟩; simp
  · simp [Lpo.nodes, Lpo.rel]; intro x hx y hy
    exact eq_iff_iff.mp (h.rel _ hx _ hy)
  · simp [Lpo.lab]; intro x; exact h.lab _
  · simp [Lpo.nodes, Lpo.form]; intro x hx; ext s
    exact eq_iff_iff.mp (congrFun (h.form _ hx) _)
  · simp [Lpo.nodes, Lpo.rel]; intro x hx
    sorry

end Lpo
