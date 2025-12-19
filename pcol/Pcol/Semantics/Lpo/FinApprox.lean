import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.Isomorphism

def Lpofin (l : Type) [Bot l] := { a : Lpo l // a.nodes.Finite }

instance {l : Type} [LE l] [Bot l] : LE (Lpofin l) where
  le a b := LE.le a.val b.val
instance {l : Type} [PartialOrder l] [OrderBot l] : Preorder (Lpofin l) :=
  Preorder.lift Subtype.val
instance {l : Type} [PartialOrder l] [OrderBot l] : PartialOrder (Lpofin l) :=
  PartialOrder.lift Subtype.val Subtype.val_injective
instance {l : Type} [Bot l] : Coe (Lpofin l) (Lpo l) where
  coe := Subtype.val

namespace Lpofin

def nodes {l : Type} [Bot l] (a : Lpofin l) := a.val.nodes
noncomputable def nodes_finset {l : Type} [Bot l] (a : Lpofin l) := a.property.toFinset
def rel {l : Type} [Bot l] (a : Lpofin l) := a.val.rel
def lab {l : Type} [Bot l] (a : Lpofin l) := a.val.lab
def form {l : Type} [Bot l] (a : Lpofin l) := a.val.form

 def IsIsomorphic {l : Type} [Bot l] (a b : Lpofin l) : Prop :=
  a.val.IsIsomorphic b.val

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by {
  constructor <;> simp [IsIsomorphic]
  -- Reflexivity
  · intro a; exact Lpo.isoEquivalence.refl a.val
  -- Symmetry
  · intro _ _ h; exact Lpo.isoEquivalence.symm h
  -- Transitivity
  · intro _ _ _ hab hbc; exact Lpo.isoEquivalence.trans hab hbc
}

instance instSetoid {l : Type} [Bot l] : Setoid (Lpofin l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

noncomputable def permute {l : Type} [Bot l] (a : Lpofin l) (e : Equiv.Perm Node) : Lpofin l :=
  ⟨ a.val.permute e, Set.Finite.image _ a.property ⟩

end Lpofin

namespace Lpo

noncomputable def trunc_base {l : Type} [Bot l] (a : Lpo l) (n : ℕ) : Lpo_base l := {
  nodes := { x ∈ a.nodes | a.rel.lev x ≤ n }
  rel x y := a.rel x y ∧ a.rel.lev x ≤ n ∧ a.rel.lev y ≤ n
  lab x := if a.rel.lev x < n then a.lab x else ⊥
  form x := if a.rel.lev x ≤ n then a.form x else Form.false
}

lemma trunc_valid {l : Type} [Bot l] (a : Lpo l) (n : ℕ) :
    is_valid_lpo (trunc_base a n) := by
  unfold trunc_base; constructor <;> simp
  · intro x y hr hx hy
    rcases a.property.rel_dom hr with ⟨hxa, hya⟩
    exact ⟨⟨hxa, hx⟩, hya, hy⟩
  · intro x hx hlev; by_cases h : x ∈ a.nodes
    · apply hx at h; exfalso; exact not_lt_of_gt hlev h
    · exact a.property.lab_dom x h
  · constructor
    · intro x y z ⟨hxy, hx, _⟩ ⟨hyz, _, hz⟩
      exact ⟨a.property.rel.trans hxy hyz, hx, hz⟩
    · intro x y ⟨hxy, _⟩ ⟨hyx, _⟩
      exact a.property.rel.antisymm hxy hyx
    · intro x ⟨hc, _⟩; exact a.property.rel.irrefl x hc
    · intro x; refine (a.property.rel.fin_prec x).subset ?_
      intro y ⟨hyx, _⟩; exact hyx
    · intro k; refine (a.property.rel.fin_lev k).subset ?_
      simp only [Set.mem_setOf_eq, Set.setOf_subset_setOf, and_imp]
      intro x hx hlev hrel; refine ⟨hx, Eq.trans ?_ hrel⟩
      refine congrArg sSup ?_; ext _; simp only [Set.mem_setOf_eq]
      refine exists_congr fun k ↦ (and_congr_right ?_); rintro rfl
      refine exists_congr fun c ↦ (and_congr_left ?_); rintro rfl
      constructor
      · intro hc k'
        refine ⟨hc k', ?_, ?_⟩ <;> refine le_trans ?_ hlev
        · refine le_of_lt (lev_mono (succ_chain_mono _ hc ?_))
          simp only [Fin.last, Fin.mk_lt_mk, Fin.is_lt]
        · by_cases heq : k'.succ = Fin.last k
          · refine le_of_eq (congrArg _ (congrArg _ heq))
          · refine le_of_lt (lev_mono (succ_chain_mono _ hc ?_))
            refine Fin.lt_def.mpr ?_; simp only [Fin.val_last]
            refine lt_of_le_of_ne (Nat.succ_le_of_lt k'.isLt) ?_
            exact (Fin.val_eq_val _ _).mp.mt heq
      · intro hc k'; exact (hc k').1
    · obtain ⟨x, hx, hroot⟩ := a.property.rel.single_rooted
      refine ⟨x, ⟨hx, ?_⟩, ?_⟩
      · exact le_of_eq_of_le (lev_root hx hroot) bot_le
      · intro y ⟨hy, hlev⟩ hne
        refine ⟨hroot _ hy hne, ?_, hlev⟩
        exact (le_of_lt (lev_mono (hroot _ hy hne))).trans hlev
  · intro x hx y hxy hlev
    rcases le_iff_lt_or_eq.mp hlev with hlev | hlev
    · exfalso; exact a.property.bot _ (hx hlev) _ hxy
    · exact lt_of_eq_of_lt hlev.symm (lev_mono hxy)
  · intro x; by_cases hlev : a.rel.lev x ≤ n <;>
      simp only [hlev, ↓reduceIte, and_false, and_true, iff_false]
    · exact a.property.form_dom x
    · simp only [Form.sat, Form.false, exists_const, not_false_eq_true]
  · intro x hx hlev; constructor
    · intro y hy
      simp only [hlev, ↓reduceIte, not_forall, Set.mem_setOf_eq] at hy
      have hsat : (a.form x).sat := Form.sat_if_vars_nonempty ⟨_, hy⟩
      have hx := (a.property.form_dom x).mp hsat
      have hyx := (a.property.form x hx).1 y hy
      refine ⟨hyx, ?_, hlev⟩
      exact (le_of_lt (lev_mono hyx)).trans hlev
    · intro z hxz hlx hlz; simp only [hlz, ↓reduceIte, hlx]
      exact (a.property.form x hx).2 z hxz

noncomputable def trunc {l : Type} [Bot l] (a : Lpo l) (n : ℕ) : Lpofin l :=
  Subtype.mk ⟨trunc_base a n, trunc_valid a n⟩ (by
    simp only [nodes, trunc_base]
    refine Set.Finite.subset (s := ⋃ k ≤ n, { x | x ∈ a.nodes ∧ a.rel.lev x = k }) ?_ ?_
    · refine Set.Finite.biUnion ?_ ?_
      · exact Set.finite_le_nat n
      · intro k _; exact a.property.rel.fin_lev k
    · intro x ⟨hx, hlev⟩
      simp only [Pi.natCast_def, Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left, exists_prop]
      obtain ⟨k, hk⟩ := lev_finite hx
      refine ⟨hx, k, ?_, hk⟩; exact ENat.coe_le_coe.mp (le_of_eq_of_le hk.symm hlev)
  )

lemma trunc_equiv {l : Type} [Bot l] {a b : Lpo l} {n : ℕ}
  (heq : a ≈ b) : trunc a n ≈ trunc b n := by {
  rcases heq with ⟨e, h⟩
  sorry
  --refine ⟨e, ?_⟩
}

lemma trunc_le {l : Type} [Preorder l] [OrderBot l] {a : Lpo l} {n : ℕ} :
  a.trunc n ≤ a := by
  constructor <;> simp [Lpo.trunc, Lpo.trunc_base, Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]
  · intro x hx y hyx; simp only [Set.mem_setOf_eq] at *
    refine ⟨(a.property.rel_dom hyx).1, ?_⟩
    exact (le_of_lt (lev_mono hyx)).trans hx.2
  · intro _ _ hxl _ _ hyl _; exact ⟨hxl, hyl⟩
  · intro x; by_cases hx : a.rel.lev x < n <;>
      unfold Lpo.rel at hx <;> simp [hx, bot_le]
  · intro _ _ h₁ h₂; exfalso; exact not_le_of_gt h₂ h₁
  · intro x hx; by_cases hlev : a.rel.lev x ≤ n
    · left; exact ⟨hx, hlev⟩
    · right; sorry

lemma trunc_mono {l : Type} [Bot l] [LE l] {a b : Lpo l} {n m : ℕ}
    (hab : a ≤ b) (hnm : n ≤ m) : a.trunc n ≤ b.trunc m := by
  constructor <;> simp only [Lpo.trunc, Lpo.trunc_base, Lpo.nodes]
  · intro x ⟨hx, hlev⟩
    refine ⟨hab.nodes hx, ?_⟩
    rw [← lev_isotone hab hx]; exact hlev.trans (Nat.cast_le.mpr hnm)
  · intro x hx y hy; sorry
  · sorry
  · sorry
  · sorry
  · sorry

lemma lpofin_level_bounded {l : Type} [Bot l] (α : Lpofin l) :
    exists n : ℕ, ∀ x ∈ α.nodes, α.rel.lev x ≤ n := by
  choose f hf using fun (x : ↑α.nodes) ↦ @lev_finite l _ α x.val x.property
  have hfin : (Set.range f).Finite := @Finite.Set.finite_range _ _ _ α.property
  have hne : hfin.toFinset.Nonempty := by
    refine (Set.Finite.toFinset_nonempty _).mpr ?_
    obtain ⟨x, hx, _⟩ := α.val.property.rel.single_rooted
    exact Set.range_nonempty_iff_nonempty.mpr ⟨x, hx⟩
  use Finset.max' hfin.toFinset hne
  intro x hx
  obtain ⟨n, hlev⟩ := lev_finite hx
  refine le_of_eq_of_le hlev (ENat.coe_le_coe.mpr ?_)
  refine Finset.le_max' _ _ ((Set.Finite.mem_toFinset _).mpr ?_)
  refine ⟨⟨x, hx⟩, ENat.coe_inj.mp ?_⟩
  exact (hf _).symm.trans hlev

lemma trunc_of_bounded {l : Type} [Bot l] {α : Lpo l} {n : ℕ}
    (hb : ∀ x ∈ α.nodes, α.rel.lev x < n) : (α.trunc n).val = α := by
  have hb' {x} (hx : x ∈ α.nodes) : α.rel.lev x ≤ n := le_of_lt (hb _ hx)
  ext x y <;>
    simp only [trunc,trunc_base, nodes, rel, lab, form] <;>
    try (refine and_iff_left_iff_imp.mpr ?_)
  · exact hb'
  · intro hxy; obtain ⟨hx, hy⟩ := α.property.rel_dom hxy
    exact ⟨hb' hx, hb' hy⟩
  · simp only [ite_eq_left_iff, not_lt]; intro hlev
    refine (α.property.lab_dom _ ?_).symm; intro c
    exact not_lt_of_ge hlev (hb _ c)
  · by_cases hx : x ∈ α.nodes
    · unfold rel at hb'; simp only [hb' hx, ↓reduceIte]
    · have : α.val.form x = Form.false := form_eq_false.mp hx
      rw [this]; simp only [ite_self]

lemma finapprox_directed {l : Type} [CompletePartialOrder l] [OrderBot l] (α : Lpo l) :
    DirectedOn LE.le { β | β ≤ α ∧ β.nodes.Finite } := by
  intro β ⟨hle, hfin⟩ β' ⟨hle', hfin'⟩
  obtain ⟨n, hn, hn'⟩ : ∃ n : ℕ,
      (∀ x ∈ β.nodes, β.rel.lev x ≤ n) ∧
      ∀ x ∈ β'.nodes, β'.rel.lev x ≤ n := by
    obtain ⟨n, hn⟩ := lpofin_level_bounded ⟨β, hfin⟩
    obtain ⟨m, hm⟩ := lpofin_level_bounded ⟨β', hfin'⟩
    refine ⟨max n m, ?_, ?_⟩
    · intro x hx; refine (hn _ hx).trans ?_
      exact ENat.coe_le_coe.mpr (le_max_left _ _)
    · intro x hx; refine (hm _ hx).trans ?_
      exact ENat.coe_le_coe.mpr (le_max_right _ _)
  -- Choose the upper bound the be α truncated to the n+1 level
  refine ⟨(α.trunc (n + 1)).val, ⟨trunc_le, ?_⟩, ?_, ?_⟩
  · exact (α.trunc (n+1)).property
  · refine le_of_eq_of_le (trunc_of_bounded ?_).symm (trunc_mono hle (le_refl _))
    intro x hx; refine lt_of_le_of_lt (hn _ hx) (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))
  · refine le_of_eq_of_le (trunc_of_bounded ?_).symm (trunc_mono hle' (le_refl _))
    intro x hx; refine lt_of_le_of_lt (hn' _ hx) (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))

theorem sup_finapprox_eq_self {l : Type} [CompletePartialOrder l] [OrderBot l] {α : Lpo l} :
    α = sSup { β | β ≤ α ∧ β.nodes.Finite } := by
  have hne : {β | β ≤ α ∧ β.nodes.Finite}.Nonempty :=
    ⟨α.trunc 0, trunc_le, (α.trunc 0 ).property⟩
  obtain ⟨_, heq⟩ := lpo_sup_of_directed (finapprox_directed α) hne
  refine Eq.trans ?_ heq.symm; unfold lpo_base_sup; ext x y
  · simp only [nodes, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx; obtain ⟨n, hlev⟩ := lev_finite hx
      refine ⟨α.trunc n, ⟨trunc_le, (α.trunc n).property⟩, ?_⟩
      simp only [nodes, trunc, Set.mem_setOf_eq]
      exact ⟨hx, le_of_eq hlev⟩
    · intro ⟨β, ⟨hle, _⟩, hx⟩; exact hle.nodes hx
  · simp only [rel, Set.mem_setOf_eq]; constructor
    · intro hxy; obtain ⟨n, hlev⟩ := lev_finite (α.property.rel_dom hxy).2
      refine ⟨α.trunc n, ⟨trunc_le, (α.trunc n).property⟩, ?_⟩
      have hy : y ∈ (α.trunc n).nodes := by
        simp only [nodes, Lpofin.nodes, trunc, Set.mem_setOf_eq]
        exact ⟨(α.property.rel_dom hxy).2, le_of_eq hlev⟩
      refine (trunc_le.rel _ ?_ _ hy).mpr hxy
      exact trunc_le.downcl _ hy _ hxy
    · intro ⟨β, ⟨hle, _⟩, hxy⟩; exact le_rel hle hxy
  · simp only [lab, Set.mem_setOf_eq]
    have hd := lpo_lab_directed (finapprox_directed α) x
    refine le_antisymm ?_ ?_
    · by_cases hx : x ∈ α.nodes
      · refine hd.le_sSup (Set.mem_setOf_eq.mpr ?_)
        obtain ⟨n, hlev⟩ := lev_finite hx
        refine ⟨α.trunc (n + 1), ⟨trunc_le, (α.trunc (n + 1)).property⟩, ?_⟩
        have hn : α.rel.lev x < ↑(n + 1) :=
          lt_of_eq_of_lt hlev (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))
        simp only [trunc, trunc_base, lab, hn, ↓reduceIte]
      · refine le_of_eq_of_le (α.property.lab_dom _ hx) bot_le
    · refine hd.sSup_le ?_
      rintro _ ⟨β, ⟨hle, _⟩, rfl⟩; exact hle.lab x
  · simp only [form, Set.mem_setOf_eq]; constructor
    · intro hform
      have hx : x ∈ α.nodes := (α.property.form_dom x).mp ⟨y, hform⟩
      obtain ⟨n, hlev⟩ := lev_finite hx
      refine ⟨α.trunc n, ⟨trunc_le, (α.trunc n).property⟩, ?_⟩
      simp only [trunc, trunc_base, form, le_of_eq hlev, ↓reduceIte]; exact hform
    · intro ⟨β, ⟨hle, _⟩, hform⟩; exact le_form hle _ hform

end Lpo
