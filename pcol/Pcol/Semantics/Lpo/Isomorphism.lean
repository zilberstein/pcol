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

def cast_perm {X X' Y Y' : Set Node} (e : X ≃ Y) (hx : X = X') (hy : Y = Y') : X' ≃ Y' := {
  toFun x := ⟨e.toFun ⟨x.val, le_of_eq hx.symm x.property⟩, le_of_eq hy (Subtype.coe_prop _)⟩
  invFun y := ⟨e.invFun ⟨y.val, le_of_eq hy.symm y.property⟩, le_of_eq hx (Subtype.coe_prop _)⟩
  left_inv := by
    intro x; simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe, Equiv.symm_apply_apply,
      Subtype.coe_eta]
  right_inv := by
    intro y; simp only [Equiv.invFun_as_coe, Subtype.coe_eta, Equiv.toFun_as_coe,
      Equiv.apply_symm_apply]
}

lemma permute_range_eq {l : Type} [Bot l] {X Y : Set Node} {a : Lpo l}
    {e : a.nodes ≃ X} {e' : a.nodes ≃ Y} (h : X = Y)
    (heq : ∀ x, (e x).val = (e' x).val) : a.permute e = a.permute e' := by
  subst h; refine congrArg _ ?_; ext x; exact heq x

noncomputable def permute' {l : Type} [Bot l] {X Y Y' : Set Node} (a : Lpo l)
    (e : X ≃ Y) (hx : a.nodes = X) (hy : Y = Y') : Lpo l :=
  a.permute (cast_perm e hx.symm hy)

lemma permute'_eq {l : Type} [Bot l] {X Y : Set Node} {a b : Lpo l}
    {e : a.nodes ≃ X} (h : a = b) (h' : X = Y) :
    a.permute e = b.permute' e (by rw [h]) h' := by
  unfold permute'; ext1 <;> subst h' <;>
    simp only [permute, Lpo.nodes, Lpo.rel, Lpo.form, Lpo.lab, cast_perm]
  · ext x y; refine exists_congr fun hx ↦ exists_congr fun hy ↦ ?_
    refine Iff.of_eq (congr (congr ?_ ?_) ?_)
    · rw [h]
    · rfl
    · rfl
  · ext x; simp only [Equiv.toFun_as_coe, Equiv.invFun_as_coe]
    nth_rewrite 1 [h]; rfl
  · ext x v; refine exists_congr fun hx ↦ ?_
    refine Iff.of_eq (congr (congr ?_ ?_) ?_)
    · rw [h]
    · rfl
    · rfl

lemma permute_convert {l : Type} [Bot l] {X Y : Set Node} (a b : Lpo l)
    {e : a.nodes ≃ X} (h : a = b) (h' : X = Y) :
    ∃ e' : b.nodes ≃ Y, a.permute e = b.permute e' := by
  subst h'
  use {
    toFun x := e ⟨x, by rw [h]; exact x.property⟩
    invFun y := ⟨e.symm y, by rw [← h]; exact Subtype.coe_prop _⟩
    left_inv := by intro x; simp only [Equiv.symm_apply_apply, Subtype.coe_eta]
    right_inv := by intro x; simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  }
  ext1
  · simp only [permute, nodes]
  · simp only [permute, rel]; ext x y; constructor <;>
      intro ⟨hx, hy, hrel⟩ <;> refine ⟨hx, hy, ?_⟩
    · nth_rewrite 1 [← h]; exact hrel
    · nth_rewrite 1 [h]; exact hrel
  · simp only [permute, lab]; ext x
    classical
    refine dite_congr rfl ?_ ?_
    · intro _; nth_rewrite 1 [h]; rfl
    · intro _; rfl
  · simp only [permute, form]; ext x v; constructor <;>
      intro ⟨hx, hform⟩ <;> refine ⟨hx, ?_⟩
    · nth_rewrite 1 [← h]; exact hform
    · nth_rewrite 1 [h]; exact hform

lemma permute_refl {l : Type} [Bot l] (a : Lpo l) :
    a.permute (Equiv.refl a.nodes) = a := by
  unfold permute; ext1 <;> simp [Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]
  · ext x y; refine ⟨fun ⟨_, _, hr⟩ ↦ hr, fun hr ↦ ⟨?_, ?_, hr⟩⟩
    · exact (a.property.rel_dom hr).1
    · exact (a.property.rel_dom hr).2
  · ext x; by_cases hx : x ∈ a.nodes
    · exact dif_pos hx
    · exact (dif_neg hx).trans (a.property.lab_dom _ hx).symm
  · ext x v; constructor
    · intro ⟨hx, hform⟩;
      have hh := a.property.form x hx
      sorry
    · intro hform; constructor
      · sorry
      · exact (a.property.form_dom x).mp ⟨_, hform⟩

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
  exact (permute'_eq h rfl).trans (permute'_eq rfl rfl)

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
    rw [permute'_eq hab rfl]; exact Eq.trans (permute'_eq rfl rfl).symm hbc

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

def perm_subset {X X' Y : Set Node} (e : X ≃ Y) (h : X' ⊆ X) :
    X' ≃ (Set.range fun x : ↑X' ↦ (e ⟨x, h x.property⟩).val) := {
  toFun x := ⟨e ⟨x, h x.property⟩, Set.mem_range.mpr ⟨_, rfl⟩⟩
  invFun y := by
    refine ⟨e.symm ⟨y, ?_⟩, ?_⟩
    · obtain ⟨_, he⟩ := Set.mem_range.mp y.property
      rw [← he]; exact Subtype.coe_prop _
    · obtain ⟨x, he⟩ := Set.mem_range.mp y.property
      have {hy} : ⟨y, hy⟩ = e ⟨x, h x.property⟩ := by
        ext; simp only; exact he.symm
      rw [this]; simp only [Equiv.symm_apply_apply, Subtype.coe_prop]
  left_inv x := by simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
  right_inv y := by simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
}

lemma perm_subset_ext {X X' Y : Set Node} {e : X ≃ Y} {h : X' ⊆ X} :
    PermExt (perm_subset e h) e := by
  constructor
  · intro x; simp only [perm_subset, Equiv.coe_fn_mk]
  · exact h

lemma perm_extend_to {X X' Y : Set Node} (Z : Set Node) (e : X ≃ Y)
    (hsub : X ⊆ X') (hd : Disjoint Y Z)
    (hdom : Cardinal.mk ↑(X' \ X) ≤ Cardinal.mk Z) :
    ∃ Z' ⊆ Z, ∃ e' : X' ≃ ↑(Y ∪ Z'), PermExt e e' := by
  obtain ⟨Z', hZ, hc⟩ :=  Cardinal.le_mk_iff_exists_subset.mp hdom
  refine ⟨Z', hZ, ?_⟩
  obtain ⟨e'⟩ := Cardinal.eq.mp hc.symm
  classical
  use {
    toFun x :=
      if hx : x.val ∈ X then
        ⟨e ⟨x, hx⟩, (Set.mem_union _ _ _).mp (Or.inl (Subtype.coe_prop _))⟩
      else
        ⟨e' ⟨x, (Set.mem_diff _).mpr ⟨x.property, hx⟩⟩, by simp⟩
    invFun x :=
      if hx : x.val ∈ Y then
        ⟨e.symm ⟨x, hx⟩, hsub (Subtype.coe_prop _)⟩
      else
        ⟨e'.symm ⟨x, (or_iff_right hx).mp ((Set.mem_union _ _ _).mp x.property)⟩,
          ((Set.mem_diff _).mp (Subtype.coe_prop _)).1⟩
    left_inv := by
      intro x; by_cases hx : x.val ∈ X
      · simp only [hx, ↓reduceDIte, Set.subset_union_left, Set.coe_inclusion, Subtype.coe_prop,
          Subtype.coe_eta, Equiv.symm_apply_apply]
      · simp only [hx, ↓reduceDIte, Set.subset_union_right, Set.coe_inclusion, Subtype.coe_eta,
          Equiv.symm_apply_apply, dite_eq_right_iff]
        intro h; exfalso; exact Set.disjoint_left.mp hd h (hZ (Subtype.coe_prop _))
    right_inv := by
      intro x; by_cases hx : x.val ∈ Y
      · simp only [hx, ↓reduceDIte, Subtype.coe_prop, Subtype.coe_eta, Equiv.apply_symm_apply]
      · simp only [hx, ↓reduceDIte, Subtype.coe_eta, Equiv.apply_symm_apply, dite_eq_right_iff]
        intro h; exfalso; exact ((Set.mem_diff _).mp (Subtype.coe_prop _)).2 h
  }
  constructor
  · intro x; simp only [Equiv.coe_fn_mk, Subtype.coe_prop, ↓reduceDIte,
      Subtype.coe_eta, Set.subset_union_left, Set.coe_inclusion]
  · exact hsub

lemma perm_extend {X X' Y : Set Node} (e : X ≃ Y) (hsub : X ⊆ X')
    (hdom : Cardinal.mk ↑(X' \ X) ≤ Cardinal.mk Y.compl) :
    ∃ Y' : Set Node, ∃ e' : X' ≃ Y', PermExt e e' := by
  have ⟨Z, _, e', hext⟩ := perm_extend_to Y.compl e hsub disjoint_compl_right hdom
  exact ⟨Y ∪ Z, e', hext⟩

lemma perm_extend' {X X' Y : Set Node} (e : X ≃ Y) (hsub : X ⊆ X')
    (hinf : Y.compl.Infinite) :
    ∃ Y' : Set Node, ∃ e' : X' ≃ Y', PermExt e e' := by
  refine perm_extend e hsub ?_
  refine le_of_le_of_eq Cardinal.mk_le_aleph0 ?_
  exact (@Cardinal.mk_eq_aleph0 _ _ hinf.to_subtype).symm

lemma permute_monotone {l : Type} [LE l] [OrderBot l] {a b : Lpo l} {X Y : Set Node}
    {e₁ : a.nodes ≃ X} {e₂ : b.nodes ≃ Y}
    (hle : a ≤ b) (hext : PermExt e₁ e₂) : a.permute e₁ ≤ b.permute e₂ := by
  unfold permute; constructor
  -- Nodes
  · simp only [Lpo.nodes]; exact hext.cod_sub
  -- Downward Closure
  · simp only [Lpo.rel, Lpo.nodes]
    intro x hx y ⟨hy, hx', hrel⟩
    refine (congrArg₂ (· ∈ ·) ?_ rfl).mp (e₁ ⟨e₂.symm ⟨y, hy⟩, ?_⟩).property
    · refine (hext.extend _).trans ?_; simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · refine hle.downcl (e₂.symm ⟨x, hx'⟩) ?_ (e₂.symm ⟨y, hy⟩) hrel
      rw [← hext.symm.extend ⟨x, hx⟩]; exact Subtype.coe_prop _
  -- Rel
  · simp only [Lpo.nodes, Lpo.rel]; intro x hx y hy
    ext; constructor
    · intro ⟨_, _, hrel⟩
      refine ⟨hext.cod_sub hx, hext.cod_sub hy, ?_⟩
      refine (congrArg₂ b.rel (hext.symm.extend ⟨x, hx⟩) (hext.symm.extend ⟨y, hy⟩)).mp ?_
      exact le_rel hle hrel
    · intro ⟨_, _, hrel⟩; refine ⟨hx, hy, ?_⟩
      refine (congrArg₂ a.rel (hext.symm.extend ⟨x, hx⟩) (hext.symm.extend ⟨y, hy⟩)).mpr ?_
      refine (hle.rel _ ?_ _ ?_).mpr hrel
      · rw [← hext.symm.extend ⟨x, hx⟩]; exact Subtype.coe_prop _
      · rw [← hext.symm.extend ⟨y, hy⟩]; exact Subtype.coe_prop _
  -- Label
  · simp only [Lpo.lab]; intro x; by_cases hx : x ∈ X
    · conv => lhs; exact dif_pos hx
      conv => rhs; exact dif_pos (hext.cod_sub hx)
      refine le_of_le_of_eq (hle.lab _) (congrArg _ ?_)
      exact hext.symm.extend _
    · refine le_of_eq_of_le (dif_neg hx) bot_le
  -- Formula
  · sorry
    -- simp only [Lpo.nodes, Lpo.form]; intro x hx; ext v; constructor
    -- intro ⟨hx, hform⟩; use hext.cod_sub hx
    -- refine
    --   ((congrArg₂ b.form ?_ ?_).trans
    --     (congrFun (hle.form _ (Subtype.coe_prop _)) _).symm).mpr hform
    -- · symm; exact hext.symm.extend _
    -- · ext y; simp only [Subtype.exists, exists_and_right, Set.mem_setOf_eq]
    --   refine exists_congr fun z ↦ ⟨?_, ?_⟩
    --   rintro ⟨⟨hz, rfl⟩, hv⟩; sorry; sorry -- THIS APPROACH IS NOT CORRECT, NEED SOMETHING ABOUT THE FREE VARS
    -- · sorry
  · simp only [Lpo.nodes, Lpo.rel]; intro x hx
    rcases hle.succ _ (e₂.symm ⟨_, hx⟩).property with hx' | ⟨z, ⟨hz, hbot⟩, hrel⟩
    · left; refine (congrArg₂ (· ∈ ·) ?_ rfl).mp (e₁ ⟨_, hx'⟩).property
      refine (hext.extend _).trans ?_; simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · right; let z' := e₁ ⟨_, hz⟩
      refine ⟨z'.val, ⟨z'.property, ?_⟩, ?_⟩
      · refine (dif_pos z'.property).trans ((congrArg _ ?_).trans hbot)
        simp only [Subtype.coe_eta, z']
        refine (congrArg Subtype.val (Equiv.symm_apply_apply _ _)).trans rfl
      · refine ⟨hext.cod_sub z'.property, hx, ?_⟩
        refine (congrArg₂ _ ?_ rfl).mpr hrel
        simp only [z']; refine (hext.symm.extend _).symm.trans ?_
        simp only [Equiv.symm_apply_apply]

end Lpo
