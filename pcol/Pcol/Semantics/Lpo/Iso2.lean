import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order

namespace Lpo

noncomputable def permute {l : Type} [Bot l] {X : Set Node} (a : Lpo l)
    (e : a.nodes ≃ X) : Lpo l := {
  val := {
    nodes := X
    rel x y := ∃ hx hy, a.rel (e.symm ⟨x, hx⟩) (e.symm ⟨y, hy⟩)
    lab x := by
      classical
      exact if hx : x ∈ X then a.lab (e.symm ⟨x, hx⟩) else ⊥
    form x v :=
      ∃ hx, a.form (e.symm ⟨x, hx⟩) { y | ∃ z : ↑X, (e.symm z).val = y ∧ z.val ∈ v }
  }
  property := by
    constructor <;> try simp
    · intro _ _ hx hy _; exact ⟨hx, hy⟩
    · intro _ hx hc; exact False.elim (hx hc)
    · constructor
      · intro _ _ _ ⟨hx, _, hxy⟩ ⟨_, hz, hyz⟩
        exact ⟨hx, hz, a.property.rel.trans hxy hyz⟩
      · intro _ _ ⟨_, _, hxy⟩ ⟨_, _, hyx⟩;
        exact congr_arg Subtype.val (Equiv.injective _ (Subtype.ext (a.property.rel.antisymm hxy hyx)))
      · intro _ ⟨_, _, hr⟩; exact a.property.rel.irrefl _ hr
      · intro x; by_cases hx : x ∈ X
        · obtain ⟨n, ⟨e'⟩⟩ :=
            finite_iff_exists_equiv_fin.mp (a.property.rel.fin_prec (e.symm ⟨x, hx⟩))
          refine finite_iff_exists_equiv_fin.mpr ⟨n, ⟨Equiv.trans ?_ e'⟩⟩
          refine Equiv.mk ?_ ?_ ?_ ?_
          · rintro ⟨y, hy⟩; simp only [Set.mem_setOf_eq] at hy
            exact ⟨e.symm ⟨y, hy.1⟩, hy.2.2⟩
          · rintro ⟨y, hy⟩; simp only [Set.mem_setOf_eq] at hy
            refine ⟨e ⟨y, ?_⟩, ?_⟩
            · exact (a.property.rel_dom hy).1
            · simp only [Set.mem_setOf_eq, Subtype.coe_eta, Equiv.symm_apply_apply,
                Subtype.coe_prop, exists_const]
              exact ⟨hx, hy⟩
          · intro x; simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.coe_eta,
              Equiv.apply_symm_apply]
          · intro x; simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.coe_eta,
             Equiv.symm_apply_apply]
        · refine (congrArg _ ?_).mp Set.finite_empty
          ext y; simp only [Set.mem_empty_iff_false, Set.mem_setOf_eq, false_iff, not_exists]
          intro hy hx'; contradiction
      · intro n
        rcases finite_iff_exists_equiv_fin.mp (a.property.rel.fin_lev n) with ⟨m, ⟨eq⟩⟩
        refine finite_iff_exists_equiv_fin.mpr ⟨m, ⟨Equiv.trans ?_ eq⟩⟩
        unfold Rel.lev; simp [Lpo.rel]; sorry
      · obtain ⟨x, hx, hroot⟩ := a.property.rel.single_rooted
        refine ⟨e ⟨x, hx⟩, ?_, ?_⟩
        · exact Subtype.coe_prop _
        · intro y hy hne; refine ⟨Subtype.coe_prop _, hy, ?_⟩
          simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
          refine hroot _ (Subtype.coe_prop _) fun hc ↦ hne ?_
          sorry
    · intro _ hlab _ hx _; exact a.property.bot _ (hlab hx) _
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
  }

def cast_perm {X Y Z : Set Node} (e : X ≃ Z) (h : X = Y) : Y ≃ Z := {
  toFun x := e.toFun ⟨x.val, by rw [h]; exact x.property⟩
  invFun y := ⟨e.invFun y, by rw [← h]; exact Subtype.coe_prop _⟩
  left_inv := by
    intro x; simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply,
      Subtype.coe_eta]
  right_inv := by
    intro y; simp only [Equiv.invFun_as_coe, Subtype.coe_eta, Equiv.toFun_as_coe,
      Equiv.apply_symm_apply]
}

noncomputable def permute' {l : Type} [Bot l] {X Y : Set Node} (a : Lpo l)
    (e : X ≃ Y) (h : a.nodes = X) : Lpo l :=
  a.permute (cast_perm e h.symm)

lemma permute'_eq {l : Type} [Bot l] {X : Set Node} {a b : Lpo l}
    {e : a.nodes ≃ X} (h : a = b) :
    a.permute e = b.permute' e (by rw [h]) := by
  unfold permute'; ext1 <;>
    simp only [permute, Lpo.nodes, Lpo.rel, Lpo.form, Lpo.lab, cast_perm]
  · ext x y; refine exists_congr fun hx ↦ exists_congr fun hy ↦ ?_
    refine Iff.of_eq (congr (congr ?_ ?_) ?_)
    · rw [h]
    · simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]
    · simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]
  · ext x; simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]
    nth_rewrite 1 [h]; rfl
  · ext x v; refine exists_congr fun hx ↦ ?_
    refine Iff.of_eq (congr (congr ?_ ?_) ?_)
    · rw [h]
    · simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]
    · simp only [Subtype.exists, Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.coe_fn_symm_mk]

lemma permute_convert {l : Type} [Bot l] {X : Set Node} (a b : Lpo l)
    {e : a.nodes ≃ X} (h : a = b) :
    ∃ e' : b.nodes ≃ X, a.permute e = b.permute e' := by
  use {
    toFun x := e ⟨x, by rw [h]; exact x.property⟩
    invFun y := ⟨e.symm y, by rw [← h]; exact Subtype.coe_prop _⟩
    left_inv := by intro x; simp only [Equiv.symm_apply_apply, Subtype.coe_eta]
    right_inv := by intro x; simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  }
  ext1
  · simp only [permute, nodes]
  · simp only [permute, rel]; sorry
  · sorry
  · sorry

lemma permute_refl {l : Type} [Bot l] (a : Lpo l) :
    a.permute (Equiv.refl a.nodes) = a := by
  unfold permute; ext1 <;> simp [Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]
  · ext x y; refine ⟨fun ⟨_, _, hr⟩ ↦ hr, fun hr ↦ ⟨?_, ?_, hr⟩⟩
    · exact (a.property.rel_dom hr).2
    · exact (a.property.rel_dom hr).1
  · ext x; simp; intro h
    exact Eq.symm (a.property.lab_dom _ h)
  · ext x v; constructor
    · intro ⟨hx, hform⟩;
      have hh := a.property.form x hx
      sorry
    · intro hform; constructor
      · exact (a.property.form_dom x).mp ⟨_, hform⟩
      · sorry

lemma permute_trans {l : Type} [Bot l] {a : Lpo l} {X Y : Set Node}
    {e₁ : a.nodes ≃ X} {e₂ : X ≃ Y} :
    (a.permute e₁).permute e₂ = a.permute (e₁.trans e₂) := by
  unfold permute; ext1
  · simp only [Lpo.nodes]
  · simp only [rel, Subtype.coe_eta, Subtype.coe_prop, exists_const, Equiv.symm_trans_apply]
    ext x y; rfl
  · simp only [lab, Subtype.coe_prop, ↓reduceDIte, Subtype.coe_eta, Equiv.symm_trans_apply]
    ext x; rfl
  · ext x v; simp only [form, Subtype.coe_eta, Subtype.exists, exists_and_right, Set.mem_setOf_eq,
      Subtype.coe_prop, exists_const, Equiv.symm_trans_apply]
    refine exists_congr fun hx ↦ Iff.of_eq (congrArg _ ?_)
    ext y; simp only [Set.mem_setOf_eq]; constructor
    · rintro ⟨z, ⟨hz, hzy⟩, w, ⟨hw, hwz⟩, hv⟩
      refine ⟨w, ⟨hw, ?_⟩, hv⟩
      refine Eq.trans (Subtype.val_inj.mpr ?_) hzy
      exact congrArg _ (Subtype.ext hwz)
    · rintro ⟨z, ⟨hz, hzy⟩, hv⟩
      refine ⟨e₂.symm ⟨z, hz⟩, ⟨Subtype.coe_prop _, hzy⟩, ?_⟩
      refine ⟨z, ⟨hz, rfl⟩, hv⟩

lemma permute_symm {l : Type} [Bot l] {a b : Lpo l} {e : a.nodes ≃ b.nodes} :
    a.permute e = b → a = b.permute e.symm := by
  intro h; refine (permute_refl a).symm.trans ?_
  rw [← Equiv.self_trans_symm e, ← permute_trans]
  exact (permute'_eq h).trans (permute'_eq rfl)

def IsIsomorphic {l : Type} [Bot l] (a b : Lpo l) : Prop :=
    ∃ (e : a.nodes ≃ b.nodes), a.permute e = b

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by
  constructor
  -- Reflexivity
  · intro a; exact ⟨Equiv.refl _, permute_refl a⟩
  -- Symmetry
  · intro a b ⟨e, hb⟩; exact ⟨e.symm, (permute_symm hb).symm⟩
  -- Transitivity
  · intro a b c ⟨e₁, hab⟩ ⟨e₂, hbc⟩
    refine ⟨e₁.trans e₂, ?_⟩; rw [← permute_trans]
    rw [permute'_eq hab]; exact Eq.trans (permute'_eq rfl).symm hbc

instance instSetoid {l : Type} [Bot l] : Setoid (Lpo l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

lemma is_isomorphic' {l : Type} [Bot l] {a b : Lpo l} {X : Set Node}
    {e : a.nodes ≃ X} (h : a.permute e = b) : a ≈ b := by
  have : X = b.nodes := by rw [← h]; simp only [permute, nodes]
  subst this; exact ⟨e, h⟩

structure PermExt {X Y A B : Set Node} (e : X ≃ A) (e' : Y ≃ B) : Prop where
  dom_sub : X ⊆ Y
  extend : ∀ x : X, (e x).val = (e' ⟨x, dom_sub x.property⟩).val

namespace PermExt

lemma cod_sub {X Y A B : Set Node} {e : X ≃ A} {e' : Y ≃ B}
    (h : PermExt e e') : A ⊆ B := by
  intro x hx
  have he := h.extend (e.symm ⟨x, hx⟩)
  simp only [Equiv.apply_symm_apply] at he; rw [he]
  refine (e' _).property

lemma symm {X Y A B : Set Node} {e : X ≃ A} {e' : Y ≃ B}
    (h : PermExt e e') : PermExt e.symm e'.symm := by
  constructor
  · intro x
    have hx := h.extend (e.symm x); simp only [Equiv.apply_symm_apply] at hx
    have heq :
       (⟨x, h.cod_sub x.property⟩ : ↑B) =
       e' ⟨e.symm x, h.dom_sub (Subtype.coe_prop _)⟩ := by
      ext; exact hx
    rw [heq]; simp only [Equiv.symm_apply_apply]

end PermExt

lemma mem_equiv {X Y : Set Node} {x : Node} {e : X ≃ Y} {hx : x ∈ X}
    (h : (e ⟨x, hx⟩).val ∈ Y) : x ∈ X := hx

lemma permute_monotone {l : Type} [Bot l] [LE l] {a b : Lpo l} {X Y : Set Node}
    {e₁ : a.nodes ≃ X} {e₂ : b.nodes ≃ Y}
    (hle : a ≤ b) (hext : PermExt e₁ e₂) : a.permute e₁ ≤ b.permute e₂ := by
  unfold permute; constructor
  · simp only [Lpo.nodes]; exact hext.cod_sub
  · simp only [Lpo.rel, Lpo.nodes]
    intro x hx y ⟨hy, hx', hrel⟩
    --refine mem_equiv ?_
    have hhh hh := hle.downcl (e₂.symm ⟨x, hx'⟩) hh (e₂.symm ⟨y, hy⟩) hrel
    sorry
  · simp only [Lpo.nodes, Lpo.rel]; intro x hx y hy
    ext; constructor
    · intro ⟨_, _, hrel⟩
      refine ⟨hext.cod_sub hx, hext.cod_sub hy, ?_⟩
      --rw [← (perm_ext_symm hext).extend ⟨x, _⟩]
      sorry
    · sorry
  · simp only [Lpo.lab]; intro x; sorry
  · simp only [Lpo.nodes, Lpo.form]; intro x hx; ext s; sorry
  · simp [Lpo.nodes, Lpo.rel]; intro x hx
    sorry

end Lpo
