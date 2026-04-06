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

noncomputable def permute {l : Type} [Bot l] (a : Lpofin l) {X : Set Node}
    (e : a.nodes ≃ X) : Lpofin l :=
--  ⟨ a.val.permute e, Set.Finite.image _ a.property ⟩
  ⟨ a.val.permute e, by {
    refine Set.finite_coe_iff.mp ?_
    refine e.finite_iff.mp ?_
    exact a.property
  }⟩

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

lemma trunc_nodes {l : Type} [Bot l] {a : Lpo l} {n : ℕ} :
    (a.trunc n).nodes = { x ∈ a.nodes | a.rel.lev x ≤ n } := rfl

lemma trunc_le {l : Type} [Preorder l] [OrderBot l] (a : Lpo l) (n : ℕ) :
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
    · right
      obtain ⟨z, hz, hzx⟩ := exists_node_lt_lev hx (lt_of_not_le hlev)
      simp only [bots, nodes, Set.mem_setOf_eq, lab, ite_eq_right_iff]
      refine ⟨z, ⟨⟨?_, ?_⟩, ?_⟩, hzx⟩
      · exact (a.property.rel_dom hzx).1
      · exact le_of_eq hz
      · intro hc; exfalso; refine ne_of_lt hc hz

lemma trunc_permute_nodes {l : Type} [Bot l] {a : Lpo l} {n : ℕ} {X : Set Node}
    {e : (a.trunc n).nodes ≃ X} :
    ((a.trunc n).val.permute e).nodes = X := rfl
lemma permute_trunc_nodes {l : Type} [Bot l] {a : Lpo l} {n : ℕ} {X : Set Node}
    {e : a.nodes ≃ X} :
    ((a.permute e).trunc n).nodes = { x ∈ X | (a.permute e).rel.lev x ≤ n } := by
  simp only [trunc, trunc_base, Lpofin.nodes, nodes]
  ext x; refine and_congr ?_ (Iff.refl _)
  simp only [permute, nodes]

lemma permute_lev {l : Type} [Bot l] {a : Lpo l} {X : Set Node} (e : a.nodes ≃ X)
    {x : Node} (hx : x ∈ a.nodes) :
    a.rel.lev x = (a.permute e).rel.lev (e ⟨x, hx⟩) := by
  simp only [permute, rel, Rel.lev]; refine congrArg _ ?_
  ext _; simp only [Set.mem_setOf_eq]
  refine exists_congr fun k ↦ and_congr (Iff.refl _) ?_
  have hlt {i : Fin (k+1)} (h : i ≠ Fin.last k) : i.val < k := by
    refine lt_of_le_of_ne ?_ ?_
    · exact Nat.le_of_lt_succ i.isLt
    · intro hc; apply h; unfold Fin.last; ext; exact hc
  constructor
  · rintro ⟨c, hc, rfl⟩
    have hi i : c i ∈ a.nodes := by
      by_cases h : i = Fin.last k
      · subst h; exact hx
      · exact (a.property.rel_dom (hc ⟨i, hlt h⟩)).1
    refine ⟨fun i ↦ e ⟨c i, hi i⟩, ?_, rfl⟩
    intro i; refine ⟨Subtype.coe_prop _, Subtype.coe_prop _, ?_⟩
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply]; exact hc i
  · rintro ⟨c, hc, heq⟩
    have hi i : c i ∈ X := by
      by_cases h : i = Fin.last k
      · subst h; conv in c _ => exact heq
        exact Subtype.coe_prop _
      · obtain ⟨hx, _⟩ := (hc ⟨i, hlt h⟩); exact hx
    refine ⟨fun i ↦ e.symm ⟨c i, hi i⟩, ?_, ?_⟩
    · intro i; simp only
      obtain ⟨_, _, h⟩ := hc i; exact h
    · simp only [FinChain.last]
      conv in c _ => exact heq
      simp only [Subtype.coe_eta, Equiv.symm_apply_apply]

lemma trunc_permute {l : Type} [Preorder l] [OrderBot l] {a : Lpo l}
    {n : ℕ} {X : Set Node} {e : a.nodes ≃ X} :
    (a.trunc n).val.permute (perm_subset e (a.trunc_le n).nodes) =
    (a.permute e).trunc n := by
  ext1
  -- Nodes
  · refine trunc_permute_nodes.trans (permute_trunc_nodes.trans ?_).symm
    ext x; simp only [Set.mem_setOf_eq, Set.mem_range, Subtype.exists]
    constructor
    · intro ⟨hx, hlev⟩; refine ⟨e.symm ⟨x, hx⟩, ?_, ?_⟩
      · simp only [trunc_base, trunc, nodes]
        refine ⟨Subtype.coe_prop _, le_of_eq_of_le ?_ hlev⟩
        rw [permute_lev e (Subtype.coe_prop _)]
        refine congrArg _ ?_;
        simp only [Subtype.coe_eta]
        refine Eq.trans (b := (Subtype.mk x hx).val) ?_ rfl
        refine congrArg _ ?_; exact Equiv.apply_symm_apply e ⟨x, hx⟩
      · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · rintro ⟨x, hx, rfl⟩; refine ⟨Subtype.coe_prop _, ?_⟩
      rw [← permute_lev]; exact hx.2
  -- Rel
  · simp only [trunc, trunc_base, rel]
    conv => lhs; simp only [permute, rel]
    ext x y; constructor
    · intro ⟨hx, hy, hrel, _⟩
      obtain ⟨⟨x, hx', hxl⟩, rfl⟩ := Set.mem_range.mp hx
      obtain ⟨⟨y, hy', hyl⟩, rfl⟩ := Set.mem_range.mp hy
      refine ⟨?_, ?_, ?_⟩
      · simp only [permute, Subtype.exists, exists_and_right, Subtype.coe_eta,
          Equiv.symm_apply_apply, Subtype.coe_prop, exists_const]
        refine (congrArg₂ _ ?_ ?_).mp hrel <;>
          simp only [perm_subset, Equiv.coe_fn_symm_mk,
            Subtype.coe_eta, Equiv.symm_apply_apply]
      · exact le_of_eq_of_le (permute_lev _ hx').symm hxl
      · exact le_of_eq_of_le (permute_lev _ hy').symm hyl
    · intro ⟨hrel, hxl, hyl⟩
      obtain ⟨hx, hy⟩ := (a.permute e).property.rel_dom hrel
      refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · refine Set.mem_range.mpr ⟨⟨e.symm ⟨x, ?_⟩, ?_, ?_⟩, ?_⟩
        · simp only [permute, nodes] at hx; exact hx
        · exact Subtype.coe_prop _
        · refine le_of_eq_of_le ?_ hxl
          refine (permute_lev e (Subtype.coe_prop _)).trans ?_
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; rfl
        · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · refine Set.mem_range.mpr ⟨⟨e.symm ⟨y, ?_⟩, ?_, ?_⟩, ?_⟩
        · simp only [permute, nodes] at hy; exact hy
        · exact Subtype.coe_prop _
        · refine le_of_eq_of_le ?_ hyl
          refine (permute_lev e (Subtype.coe_prop _)).trans ?_
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; rfl
        · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · simp only [perm_subset, Equiv.coe_fn_symm_mk]
        exact hrel.2.2
      · refine le_of_eq_of_le ?_ hxl
        simp only [perm_subset, Equiv.coe_fn_symm_mk]
        refine (permute_lev e (Subtype.coe_prop _)).trans ?_
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; rfl
      · refine le_of_eq_of_le ?_ hyl
        simp only [perm_subset, Equiv.coe_fn_symm_mk]
        refine (permute_lev e (Subtype.coe_prop _)).trans ?_
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]; rfl
  -- Label
  · simp only [trunc, trunc_base, lab]
    conv => lhs; simp only [permute, perm_subset, Equiv.coe_fn_symm_mk, Set.mem_range,
      Subtype.exists, lab, exists_and_right]
    ext x; by_cases hx : x ∈ X
    · by_cases hlev : a.rel.lev (e.symm ⟨x, hx⟩) ≤ n
      · refine (dif_pos ?_).trans ?_
        · refine Set.mem_range.mpr ⟨⟨e.symm ⟨x, hx⟩, ?_, hlev⟩, ?_⟩
          · exact Subtype.coe_prop _
          · simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
        · refine if_congr ?_ ?_ rfl
          · refine Iff.of_eq (congrArg₂ LT.lt ?_ rfl)
            refine (permute_lev e (Subtype.coe_prop _)).trans ?_
            simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
          · simp only [permute, lab, dif_pos hx]
      · refine (dif_neg ?_).trans ((dif_neg ?_).trans (Eq.refl ⊥)).symm
        · refine Set.mem_range.mp.mt ?_
          simp only [nodes, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, not_exists]
          intro y ⟨hy, hlevy⟩ hc; apply hlev
          have : ⟨x, hx⟩ = e ⟨y, hy⟩ := by ext; exact hc.symm
          rw [this]; simp only [Equiv.symm_apply_apply]; exact hlevy
        · intro hc; apply hlev; refine le_of_eq_of_le ?_ (le_of_lt hc)
          refine (permute_lev e (Subtype.coe_prop _)).trans ?_
          simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · refine Eq.trans ?_ ?_ (b := ⊥)
      · refine dif_neg ?_
        refine Set.mem_range.mp.mt ?_
        simp only [nodes, Set.coe_setOf, Set.mem_setOf_eq, Subtype.exists, not_exists]
        rintro y ⟨hy, hlev⟩ rfl; exact hx (Subtype.coe_prop _)
      · refine ((if_congr (Iff.refl _) ?_ rfl).trans (ite_id ⊥)).symm
        exact (a.permute e).property.lab_dom _ hx
  -- Formula
  · simp only [form, trunc, trunc_base]
    conv => lhs; simp only [permute, form]
    ext x v; constructor
    · intro ⟨hx, hh⟩; sorry
    · sorry

lemma trunc_equiv {l : Type} [Preorder l] [OrderBot l] {a b : Lpo l} {n : ℕ}
    (heq : a ≈ b) : trunc a n ≈ trunc b n := by
  obtain ⟨e, h⟩ := heq
  refine is_isomorphic' (e := perm_subset e (a.trunc_le n).nodes) ?_
  conv => rhs; rw [← h]
  exact trunc_permute

lemma trunc_mono {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {n m : ℕ}
    (hab : a ≤ b) (hnm : n ≤ m) : a.trunc n ≤ b.trunc m := by
  constructor <;>
  simp only [Lpo.trunc, Lpo.trunc_base, Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]
  · intro x ⟨hx, hlev⟩
    refine ⟨hab.nodes hx, ?_⟩
    exact le_of_eq_of_le (lev_isotone hab hx).symm (hlev.trans (Nat.cast_le.mpr hnm))
  · intro x ⟨hx, hlx⟩ y ⟨hyx, hly, hh⟩
    have hy := hab.downcl _ hx _ hyx
    refine ⟨hy, ?_⟩
    refine le_trans (le_of_lt (lev_mono ?_)) hlx
    exact (hab.rel _ hy _ hx).mpr hyx
  · intro x ⟨hx, hlx⟩ y ⟨hy, hly⟩
    refine congrArg₂ And ?_ (congrArg₂ And ?_ ?_)
    · exact hab.rel _ hx _ hy
    · simp only [hlx, eq_iff_iff, true_iff]
      refine le_of_eq_of_le (lev_isotone hab hx).symm ?_
      exact hlx.trans (ENat.coe_le_coe.mpr hnm)
    · simp only [hly, eq_iff_iff, true_iff]
      refine le_of_eq_of_le (lev_isotone hab hy).symm ?_
      exact hly.trans (ENat.coe_le_coe.mpr hnm)
  · intro x; by_cases hx : x ∈ a.nodes
    · by_cases h : a.val.rel.lev x < n <;>
       simp only [h, ↓reduceIte]
      · have hb : b.val.rel.lev x < m := by
          refine lt_of_eq_of_lt (lev_isotone hab hx).symm ?_
          exact lt_of_lt_of_le h (ENat.coe_le_coe.mpr hnm)
        simp only [hb, ↓reduceIte, ge_iff_le]
        exact hab.lab x
      · exact bot_le
    · rw [a.property.lab_dom _ hx]; simp only [ite_self, bot_le]
  · intro x ⟨hx, hlev⟩
    have hlev' : b.val.rel.lev x ≤ m := by
      refine le_of_eq_of_le (lev_isotone hab hx).symm ?_
      exact hlev.trans (ENat.coe_le_coe.mpr hnm)
    simp only [hlev, ↓reduceIte, hlev']
    exact hab.form _ hx
  · intro x ⟨hx, hlev⟩
    rcases hab.succ x hx with hx | ⟨z, hz, hzx⟩
    · rcases (trunc_le a n).succ x hx with hx' | ⟨w, hw, hwx⟩
      · left; exact hx'
      · right; refine ⟨w, hw, ?_⟩
        refine ⟨le_rel hab hwx, ?_, hlev⟩
        have hw' : w ∈ b.nodes :=
          hab.nodes ((trunc_le a n).nodes hw.1)
        exact (le_of_lt (lev_mono (le_rel hab hwx))).trans hlev
    · right; rcases (trunc_le a n).succ z hz.1 with hz' | ⟨w, hw, hwz⟩
      · refine ⟨z, ⟨hz', ?_⟩, hzx, ?_, hlev⟩
        · exact eq_bot_iff.mpr (le_of_le_of_eq ((trunc_le a n).lab z) hz.2)
        · exact (le_of_lt (lev_mono hzx)).trans hlev
      · have hwx := b.property.rel.trans (le_rel hab hwz) hzx
        refine ⟨w, hw, hwx, ?_, hlev⟩
        exact (le_of_lt (lev_mono hwx)).trans hlev

lemma trunc_le_trunc {l : Type} [Preorder l] [OrderBot l] {α β : Lpo l} {n : ℕ}
    (h : α.trunc n ≤ β) : α.trunc n ≤ β.trunc n := by
  have hsub : (α.trunc n).nodes ⊆ (β.trunc n).nodes := by
    intro x hx; refine ⟨h.nodes hx, ?_⟩
    have := lev_isotone h hx; rw [← this]
    have := lev_isotone (trunc_le α n) hx; rw [this]
    exact hx.2
  constructor
  · exact hsub
  · intro x hx y hrel; exact h.downcl x hx y (le_rel (trunc_le β n) hrel)
  · intro x hx y hy
    refine (h.rel _ hx _ hy).trans ((trunc_le _ _).rel _ ?_ _ ?_).symm <;>
      refine hsub ?_ <;> assumption
  · intro x; by_cases hx : x ∈ (α.trunc n).nodes
    · by_cases hlev : β.rel.lev x < n
      · conv => rhs; exact if_pos hlev
        exact h.lab x
      · have := lev_isotone h hx ; rw [← this] at hlev
        have := lev_isotone (trunc_le α n) hx; rw [this] at hlev
        exact le_of_eq_of_le (if_neg hlev) bot_le
    · exact le_of_eq_of_le ((α.trunc n).val.property.lab_dom _ hx) bot_le
  · intro x hx
    exact (h.form _ hx).trans ((trunc_le _ _).form _ (hsub hx)).symm
  · intro x hx
    rcases h.succ x hx.1 with hx' | ⟨z, hz, hrel⟩
    · left; exact hx'
    · right; refine ⟨z, hz, ((trunc_le _ _).rel _ ?_ _ ?_).mpr hrel⟩
      · exact hsub hz.1
      · exact hx

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

lemma finapprox_directed {l : Type} [PartialOrder l] [OrderBot l] (α : Lpo l) :
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
  refine ⟨(α.trunc (n + 1)).val, ⟨trunc_le _ _, ?_⟩, ?_, ?_⟩
  · exact (α.trunc (n+1)).property
  · refine le_of_eq_of_le (trunc_of_bounded ?_).symm (trunc_mono hle (le_refl _))
    intro x hx; refine lt_of_le_of_lt (hn _ hx) (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))
  · refine le_of_eq_of_le (trunc_of_bounded ?_).symm (trunc_mono hle' (le_refl _))
    intro x hx; refine lt_of_le_of_lt (hn' _ hx) (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))

lemma finapprox_nonempty {l : Type} [Preorder l] [OrderBot l] (α : Lpo l) :
    { β | β ≤ α ∧ β.nodes.Finite }.Nonempty :=
  ⟨α.trunc 0, trunc_le _ _, (α.trunc 0 ).property⟩

def finapprox {l : Type} [PartialOrder l] [OrderBot l] (α : Lpo l) : DSet (Lpo l) := {
  val := { β | β ≤ α ∧ β.nodes.Finite }
  property := ⟨finapprox_directed α, finapprox_nonempty α⟩
}

def finapprox' {l : Type} [PartialOrder l] [OrderBot l] (α : Lpo l) : DSet (Lpofin l) := {
  val := { β : Lpofin l | β.val ≤ α }
  property := by
    constructor
    · have hd := finapprox_directed α
      intro β₁ h₁ β₂ h₂
      obtain ⟨γ, ⟨hle, hfin⟩, hle₁, hle₂⟩ :=
        hd β₁.val ⟨h₁, β₁.property⟩ β₂.val ⟨h₂, β₂.property⟩
      exact ⟨⟨γ, hfin⟩, hle, hle₁, hle₂⟩
    · obtain ⟨β, hle, hfin⟩ := finapprox_nonempty α
      exact ⟨⟨β, hfin⟩, hle⟩
}

lemma finapprox_convert  {l : Type} [PartialOrder l] [OrderBot l]
    {α : Lpo l} {α' : Lpofin l} :
    α'.val ∈ α.finapprox ↔ α' ∈ α.finapprox' := by
  constructor
  · intro ⟨hle, _⟩; exact hle
  · intro hle; exact ⟨hle, α'.property⟩

lemma finapprox'_mono {l : Type} [PartialOrder l] [OrderBot l] :
    @Monotone (Lpo l) (DSet (Lpofin l)) _ _ finapprox' := by
  intro α β hle γ hγ; exact hγ.trans hle

theorem sup_finapprox_eq_self {l : Type} [DCPO l] [OrderBot l] {α : Lpo l} :
    α = (finapprox α).dSup := by
  simp [DSet.dSup, DCPO.dSup, lpo_base_sup]; ext x y
  · simp only [nodes, Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
    constructor
    · intro hx; obtain ⟨n, hlev⟩ := lev_finite hx
      refine ⟨α.trunc n, ⟨trunc_le _ _, (α.trunc n).property⟩, ?_⟩
      simp only [nodes, trunc, Set.mem_setOf_eq]
      exact ⟨hx, le_of_eq hlev⟩
    · intro ⟨β, ⟨hle, _⟩, hx⟩; exact hle.nodes hx
  · simp only [rel, Set.mem_setOf_eq]; constructor
    · intro hxy; obtain ⟨n, hlev⟩ := lev_finite (α.property.rel_dom hxy).2
      refine ⟨α.trunc n, ⟨trunc_le _ _, (α.trunc n).property⟩, ?_⟩
      have hy : y ∈ (α.trunc n).nodes := by
        simp only [nodes, Lpofin.nodes, trunc, Set.mem_setOf_eq]
        exact ⟨(α.property.rel_dom hxy).2, le_of_eq hlev⟩
      refine ((trunc_le _ _).rel _ ?_ _ hy).mpr hxy
      exact (trunc_le _ _).downcl _ hy _ hxy
    · intro ⟨β, ⟨hle, _⟩, hxy⟩; exact le_rel hle hxy
  · simp only [lab, Set.mem_setOf_eq]
    refine le_antisymm ?_ ?_
    · by_cases hx : x ∈ α.nodes
      · refine DSet.le_dSup (Set.mem_setOf_eq.mpr ?_)
        obtain ⟨n, hlev⟩ := lev_finite hx
        refine ⟨α.trunc (n + 1), ⟨trunc_le _ _, (α.trunc (n + 1)).property⟩, ?_⟩
        have hn : α.rel.lev x < ↑(n + 1) :=
          lt_of_eq_of_lt hlev (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))
        simp only [trunc, trunc_base, lab, hn, ↓reduceIte]
      · refine le_of_eq_of_le (α.property.lab_dom _ hx) bot_le
    · refine DSet.dSup_le ?_
      rintro _ ⟨β, ⟨hle, _⟩, rfl⟩; exact hle.lab x
  · simp only [form, Set.mem_setOf_eq]; constructor
    · intro hform
      have hx : x ∈ α.nodes := (α.property.form_dom x).mp ⟨y, hform⟩
      obtain ⟨n, hlev⟩ := lev_finite hx
      refine ⟨α.trunc n, ⟨trunc_le _ _, (α.trunc n).property⟩, ?_⟩
      simp only [trunc, trunc_base, form, le_of_eq hlev, ↓reduceIte]; exact hform
    · intro ⟨β, ⟨hle, _⟩, hform⟩; exact le_form hle _ hform

open OmegaCompletePartialOrder

noncomputable def trunc_chain {l : Type} [PartialOrder l] [OrderBot l] (α : Lpo l) :
    Chain (Lpo l) := {
  toFun n := α.trunc n
  monotone' := by
    intro n m hle; exact trunc_mono (le_refl _) hle
}

lemma trunc_chain_sup {l : Type} [DCPO l] [OrderBot l] (α : Lpo l) :
    α = ωSup α.trunc_chain := by
  ext1
  -- NODES
  · rw [ωSup_nodes]; ext x; simp only [Set.mem_iUnion, trunc_chain, trunc, trunc_base]
    constructor
    · intro hx; obtain ⟨n, hlev⟩ := lev_finite hx
      exact ⟨n, hx, le_of_eq hlev⟩
    · rintro ⟨_, hx, _⟩; exact hx
  -- REL
  · rw [ωSup_rel]; ext x y
    simp only [trunc_chain, trunc, trunc_base]; constructor
    · intro hrel; obtain ⟨hx, hy⟩ := α.property.rel_dom hrel
      obtain ⟨i, hi⟩ := lev_finite hx
      obtain ⟨j, hj⟩ := lev_finite hy
      refine ⟨max i j, hrel, ?_, ?_⟩
      · refine le_of_eq_of_le hi (ENat.coe_le_coe.mpr le_sup_left)
      · refine le_of_eq_of_le hj (ENat.coe_le_coe.mpr le_sup_right)
    · rintro ⟨_, hrel, _⟩; exact hrel
  -- LABEL
  · rw [ωSup_lab]; ext x; simp only [trunc_chain, trunc, trunc_base]
    by_cases hx : x ∈ α.nodes
    · refine le_antisymm ?_ ?_
      · obtain ⟨n, hlev⟩ := lev_finite hx
        refine le_of_eq_of_le ?_ (le_ωSup _ (n + 1))
        refine (if_pos ?_).symm
        exact lt_of_eq_of_lt hlev (ENat.coe_lt_coe.mpr (Nat.lt_succ_self _))
      · refine ωSup_le _ _ fun i ↦ ?_; by_cases hi : α.rel.lev x < i
        · exact le_of_eq (if_pos hi)
        · exact le_of_eq_of_le (if_neg hi) bot_le
    · refine (α.property.lab_dom _ hx).trans (bot_unique ?_).symm
      refine ωSup_le _ _ fun i ↦ le_bot_iff.mpr ?_
      refine (if_congr (Iff.refl _) ?_ rfl).trans (ite_self _)
      exact α.property.lab_dom _ hx
  -- FORMULA
  · rw [ωSup_form]; ext x v; simp only [trunc_chain, trunc, trunc_base]
    constructor
    · intro hform; have hx := (α.property.form_dom _).mp ⟨_, hform⟩
      obtain ⟨n, hlev⟩ := lev_finite hx
      refine ⟨n, (congrFun (if_pos ?_) _).mpr hform⟩
      exact le_of_eq hlev
    · intro ⟨i, hform⟩; by_cases hi : α.rel.lev x ≤ i
      · exact (congrFun (if_pos hi) _).mp hform
      · exfalso; exact (congrFun (if_neg hi) _).mp hform

lemma permute_inv {l : Type} [DCPO l] [OrderBot l]
    (c₁ c₂ : Chain (Lpo l))
    (en : (n : ℕ) → (c₁ n).nodes ≃ (c₂ n).nodes)
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    ∀ n m x {hx}, ((en n).symm ⟨en m x, hx⟩).val = x.val := by
  intro n m x hx; by_cases h : n ≤ m
  · refine ((he h).symm.extend _).trans ?_
    simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
  · have h := (not_le.mp h).le
    have hex := (he h).extend x
    have hx' := (c₁.monotone' h).nodes x.property
    have :
        (⟨↑((en m) x), hx⟩ : (c₂ n).nodes) =
        ⟨↑((en n) ⟨x, hx'⟩), Subtype.coe_prop _⟩ := by
      ext; exact hex
    rw [this]; simp only [Subtype.coe_eta, Equiv.symm_apply_apply]

lemma permute_inv' {l : Type} [DCPO l] [OrderBot l]
    (c₁ c₂ : Chain (Lpo l))
    (en : (n : ℕ) → (c₁ n).nodes ≃ (c₂ n).nodes)
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    ∀ n m x {hx}, (en n ⟨(en m).symm x, hx⟩).val = x.val := by
  intro n m x hx
  refine Eq.trans ?_ (permute_inv c₂ c₁ (fun n ↦ (en n).symm) ?_ n m x (hx := hx))
  · simp only [Equiv.symm_symm]
  · intro _ _ hle; exact (he hle).symm

-- Construct the supremum of a chain of permutations
noncomputable def permute_sup {l : Type} [DCPO l] [OrderBot l]
    (c₁ c₂ : Chain (Lpo l))
    {en : (n : ℕ) → (c₁ n).nodes ≃ (c₂ n).nodes}
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    (ωSup c₁).nodes ≃ (ωSup c₂).nodes := {
  toFun x := by
    obtain ⟨x, hx⟩ := x
    simp only [ωSup_nodes, Set.mem_iUnion] at hx
    let n := hx.choose
    refine ⟨en hx.choose ⟨x, hx.choose_spec⟩, ?_⟩
    exact (le_ωSup c₂ n).nodes (Subtype.coe_prop _)
  invFun y := by
    obtain ⟨y, hy⟩ := y
    simp only [ωSup_nodes, Set.mem_iUnion] at hy
    let n := hy.choose
    refine ⟨(en n).symm ⟨y, hy.choose_spec⟩, ?_⟩
    exact (le_ωSup c₁ n).nodes (Subtype.coe_prop _)
  left_inv := by
    intro x; ext; exact permute_inv c₁ c₂ en he _ _ _
  right_inv := by
    intro x; ext; simp; exact permute_inv' c₁ c₂ en he _ _ _
}

lemma le_permute_sup {l : Type} [DCPO l] [OrderBot l]
    {c₁ c₂ : Chain (Lpo l)}
    {en : (n : ℕ) → (c₁ n).nodes ≃ (c₂ n).nodes}
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    ∀ i, PermExt (en i) (permute_sup c₁ c₂ he) := by
  intro i; constructor
  · intro x; simp only [permute_sup, Equiv.coe_fn_mk]
    have {j hj} : ((en i) x).val = ((en j) ⟨x, hj⟩).val := by
      by_cases h : i ≤ j
      · exact ((he h).extend ⟨x.val, _⟩)
      · refine ((@he j i ?_).extend ⟨x.val, _⟩).symm
        linarith
    exact this
  · exact (le_ωSup c₁ i).nodes

lemma permute_continuous {l : Type} [DCPO l] [OrderBot l]
    {c₁ c₂ : Chain (Lpo l)}
    {en : (n : ℕ) → (c₁ n).nodes ≃ (c₂ n).nodes}
    (hp : ∀ i, (c₁ i).permute (en i) = c₂ i)
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    (ωSup c₁).permute (permute_sup c₁ c₂ he) = ωSup c₂ := by
  ext1
  -- NODES
  · conv => lhs; simp only [permute, nodes]
    rfl
  -- REL
  · conv => lhs; simp only [permute, rel]
    conv => rhs; exact ωSup_rel
    ext x y; constructor
    · intro ⟨_, _, hrel⟩
      have ⟨i, hrel⟩ := (congrFun (congrFun ωSup_rel _) _).mp hrel
      use i; rw [← hp i]; simp only [permute, rel]
      obtain ⟨hx, hy⟩ := (c₁ i).property.rel_dom hrel
      refine ⟨?_, ?_, ?_⟩
      · refine (congrArg₂ (· ∈ ·) ?_ rfl).mp (en i ⟨_, hx⟩).property
        refine ((le_permute_sup he i).extend _).trans ?_
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · refine (congrArg₂ (· ∈ ·) ?_ rfl).mp (en i ⟨_, hy⟩).property
        refine ((le_permute_sup he i).extend _).trans ?_
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
      · refine (congrArg₂ _ ?_ ?_).mp hrel
        · symm; exact (le_permute_sup he i).symm.extend ⟨x, _⟩
        · symm; exact (le_permute_sup he i).symm.extend ⟨y, _⟩
    · intro ⟨i, hrel⟩; rw [← hp i] at hrel
      simp only [permute, rel] at hrel
      obtain ⟨hx, hy, hrel⟩ := hrel
      refine ⟨(le_ωSup c₂ i).nodes hx, (le_ωSup c₂ i).nodes hy, ?_⟩
      refine le_rel (le_ωSup c₁ i) ?_; refine (congrArg₂ _ ?_ ?_).mp hrel
      · exact (le_permute_sup he i).symm.extend ⟨x, _⟩
      · exact (le_permute_sup he i).symm.extend ⟨y, _⟩
  -- LABEL
  · conv => lhs; simp only [permute, lab]
    conv => rhs; exact ωSup_lab
    ext x; by_cases hx : x ∈ (ωSup c₂).nodes
    · conv => lhs; exact dif_pos hx
      refine (congrFun ωSup_lab _).trans (congrArg _ ?_)
      ext i; simp only [OrderHom.coe_mk]
      rw [← hp i]; simp only [permute, lab]
      by_cases hx : x ∈ (c₂ i).nodes
      · conv => rhs; exact dif_pos hx
        refine congrArg _ ?_
        symm; exact (le_permute_sup he i).symm.extend ⟨x, _⟩
      · conv => rhs; exact dif_neg hx
        refine (c₁ i).property.lab_dom _ fun hcn ↦ hx ?_
        refine (congrArg₂ (· ∈ ·) ?_ rfl).mp (en i ⟨_, hcn⟩).property
        refine ((le_permute_sup he i).extend _).trans ?_
        simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
    · conv => lhs; exact dif_neg hx
      symm; refine bot_unique (ωSup_le _ _ fun i ↦ le_bot_iff.mpr ?_)
      refine (c₂ i).property.lab_dom _ fun c ↦ hx ?_
      exact (le_ωSup c₂ i).nodes c
  -- FORMULA
  · sorry

lemma permute_chain {l : Type} [DCPO l] [OrderBot l]
    {α : Lpo l} {c : Chain (Lpo l)}
    {en : (n : ℕ) → (α.trunc n).nodes ≃ (c n).nodes}
    (hc : ∀ i, c i = (α.trunc i).permute (en i))
    (he : ∀ {i j}, i ≤ j → PermExt (en i) (en j)) :
    α ≈ ωSup c := by
  rw [α.trunc_chain_sup]
  use permute_sup α.trunc_chain c he
  refine permute_continuous ?_ he
  intro i; simp only [trunc_chain]; exact (hc i).symm

end Lpo
