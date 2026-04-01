import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.Isomorphism
import Pcol.Semantics.Lpo.FinApprox

def Pom (l : Type) [Bot l] : Type := Quotient (@Lpo.instSetoid l _)

namespace Pom

def mk {l : Type} [Bot l] : Lpo l → Pom l := Quotient.mk'

instance {l : Type} [Bot l] : Membership (Lpo l) (Pom l) where
  mem p α := p = Pom.mk α

instance {l : Type} [LE l] [Bot l] : LE (Pom l) where
  le p q := ∃ a ∈ p, ∃ b ∈ q, a ≤ b

open Cardinal

def card {l : Type} [Bot l] (p : Pom l) : Cardinal :=
    p.lift (fun α ↦ Cardinal.mk α.nodes) (by {
      intro α β ⟨e, _⟩; exact Cardinal.eq.mpr ⟨e⟩
    })

lemma le_lpo {l : Type} [LE l] [OrderBot l] {q : Pom l} {α : Lpo l}
    (hinf : α.nodes.compl.Infinite) (hle : Pom.mk α ≤ q) :
    ∃ β ∈ q, α ≤ β := by
  obtain ⟨α', heq, β', rfl, hle⟩ := hle
  obtain ⟨e, hp⟩ := Quotient.eq_iff_equiv.mp heq
  obtain ⟨Y, e', hex⟩ := Lpo.perm_extend' e.symm hle.nodes hinf
  refine ⟨β'.permute e', ?_, ?_⟩
  · exact Quotient.eq_iff_equiv.mpr ⟨e', rfl⟩
  · refine le_of_eq_of_le ?_ (Lpo.permute_monotone hle hex)
    exact Lpo.permute_symm hp

lemma ge_lpo {l : Type} [LE l] [OrderBot l] {p : Pom l} {β : Lpo l}
    (hle : p ≤ Pom.mk β) : ∃ α ∈ p, α ≤ β := by
  obtain ⟨α', rfl, β', heq, hle⟩ := hle
  obtain ⟨e, hp⟩ := Quotient.eq_iff_equiv.mp heq.symm
  let e' := Lpo.perm_subset e hle.nodes
  refine ⟨α'.permute e', ?_, ?_⟩
  · exact Quotient.eq_iff_equiv.mpr ⟨e', rfl⟩
  · refine le_of_le_of_eq ?_ hp
    exact Lpo.permute_monotone hle Lpo.perm_subset_ext

def singleton {l : Type} [Bot l] (ℓ : l) : Pom l :=
  Pom.mk (Lpo.singleton default ℓ)

end Pom

instance {l : Type} [Bot l] : Bot (Pom l) where
  bot := Pom.singleton ⊥

instance {l : Type} [LE l] [OrderBot l] : OrderBot (Pom l) where
  bot_le p := by {
    obtain ⟨a, ha⟩ := p.exists_rep
    obtain ⟨x, hnodes⟩ := a.property.rel.single_rooted
    sorry
--    refine ⟨Lpo.singleton x ⊥, ?_, a, ?_, ?_⟩
    -- · have hx : x ∈ a.nodes := by sorry
    --   constructor
    --   · simp [Lpo.singleton, Lpo.nodes]; exact hx
    --   · simp [Lpo.singleton, Lpo.nodes]; intro y hx z; sorry
    --   · sorry
    --   · sorry
    --   · sorry
    --   · sorry
    -- · simp [Bot.bot, Pom.singleton]; refine Quotient.sound ?_
    --   sorry
    -- · rw [← ha]; rfl
  }

instance {l : Type} [PartialOrder l] [OrderBot l] : Preorder (Pom l) where
  le_refl p := by
    rcases Quotient.exists_rep p with ⟨a, ha⟩
    exact ⟨a, Eq.symm ha, a, Eq.symm ha, le_refl _⟩

  le_trans p q r := by
    rintro hle ⟨β, rfl, γ, rfl, hle₂⟩
    obtain ⟨α, rfl, hle₁⟩ := Pom.ge_lpo hle
    refine ⟨α, rfl, γ, rfl, hle₁.trans hle₂⟩

lemma permute_le_lev_nodes {l : Type} [LE l] [Bot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} {n : ℕ} (h : α.permute e ≤ α) :
    { x ∈ α.nodes | α.rel.lev x = n} =
    { x ∈ (α.permute e).nodes | (α.permute e).rel.lev x = n } := by
  symm; refine Set.Finite.eq_of_subset_of_card_le ?_ ?_ ?_
  · exact α.property.rel.fin_lev n
  · intro x ⟨hx, hlev⟩; refine ⟨h.nodes hx, Eq.trans ?_ hlev⟩
    refine (lev_isotone h hx).symm
  · obtain ⟨k, ⟨efin⟩⟩ := (α.property.rel.fin_lev n).exists_equiv_fin
    let e' :
        { x | x ∈ α.nodes ∧ α.rel.lev x = n } ≃
        { x | x ∈ (α.permute e).nodes ∧ (α.permute e).rel.lev x = n } := {
      toFun x := ⟨e ⟨x, x.property.1⟩, ⟨Subtype.coe_prop _, Eq.trans (Lpo.permute_lev _ _).symm x.property.2⟩⟩
      invFun y := ⟨e.symm ⟨y, y.property.1⟩, by {
        refine ⟨Subtype.coe_prop _, Eq.trans ?_ y.property.2⟩
        refine (Lpo.permute_lev e (Subtype.coe_prop _)).trans ?_
        simp only [Set.mem_setOf_eq, Subtype.coe_eta, Equiv.apply_symm_apply]
      }⟩
      left_inv _ := by simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.coe_eta,
        Equiv.symm_apply_apply, Set.sep_subset, Set.coe_inclusion]
      right_inv _ := by simp only [Set.coe_setOf, Set.mem_setOf_eq, Subtype.coe_eta,
        Equiv.apply_symm_apply]
    }
    refine le_of_eq (Eq.trans (b := k) ?_ (Eq.symm ?_)) <;> refine Nat.card_eq_of_equiv_fin ?_
    · exact efin
    · exact e'.symm.trans efin

lemma permute_le_self_nodes {l : Type} [LE l] [Bot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} (h : α.permute e ≤ α) : α.nodes = (α.permute e).nodes := by
  have {β : Lpo l} : β.nodes = ⋃ n : ℕ, { x ∈ β.nodes | β.rel.lev x = n } := by
    ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left, iff_self_and]
    exact lev_finite
  refine this.trans (this.trans ?_).symm; refine iSup_congr fun i ↦ ?_
  symm; exact permute_le_lev_nodes h

-- The reverse inequality is immediate, but this direction requires us to show that
-- there is a finite chain of permutations from x -> e x -> e (e x) -> .. -> e.symm x
-- such that the labels are monotonically increasing in the chain. Such a chain must
-- exist because permuting a node keeps it within the same (finite) level, therefore
-- eventually the permutations must either reach e.symm x, or form a cycle. In the
-- case of a cycle, we must have some node z such that e z = x and lab (e z) ≤ lab x,
-- therefore z = e.symm x, so it is also reached
lemma permute_le_self_lab {l : Type} [PartialOrder l] [OrderBot l] {α : Lpo l}
    {e : α.nodes ≃ α.nodes} (hle : α.permute e ≤ α) {x : Node} (hx : x ∈ α.nodes) :
    α.lab x ≤ (α.permute e).lab x := by
  obtain ⟨i, hlev⟩ := lev_finite hx
  obtain ⟨n, ⟨e'⟩⟩ := (α.property.rel.fin_lev i).exists_equiv_fin
  have hlab {z} (hz : z ∈ α.nodes) := hle.lab (e ⟨_, hz⟩)
  simp only [Lpo.lab, Lpo.permute, Subtype.exists, exists_and_right, Subtype.coe_prop,
    ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply] at hlab
  simp only [Lpo.permute, Lpo.lab, dif_pos hx]
  have hn : 1 ≤ n := by
    refine Nat.succ_le_of_lt ?_
    exact lt_of_le_of_lt bot_le ((e' ⟨x, hx, hlev⟩).isLt)
  have hxl : α.rel.lev (e.symm ⟨x, hx⟩) = i := by
    refine (Lpo.permute_lev e (Subtype.coe_prop _)).trans
      (Eq.trans ?_
        ((Set.ext_iff.mp (permute_le_lev_nodes hle (n := i)) x).mp ⟨hx, hlev⟩).2)
    simp only [Subtype.coe_eta, Equiv.apply_symm_apply]
  have build_chain (k : ℕ)
      (f : FinChain (n - k - 1) { x : Node // x ∈ α.nodes ∧ α.rel.lev x = i})
      (hfirst : f.first.val = x)
      (mono : ∀ {i j}, i ≤ j → α.lab (f i) ≤ α.lab (f j))
      (next : Rel.is_succ_chain (fun y z ↦ z.val = (e ⟨y.val, y.property.1⟩).val) f)
      (inj : Function.Injective f) :
      α.lab x ≤ α.lab (e.symm ⟨x, hx⟩).val := by
    revert f; induction k with
    | zero =>
      simp only [Nat.sub_zero]; intro f first mono _ inj
      -- e.symm x must be in the chain since there are n unique elements
      conv at e' => rhs; rw [← Nat.sub_add_cancel hn]
      subst first
      -- k is the index of e.symm x
      obtain ⟨k, hk⟩ :=
        (Finite.injective_iff_surjective_of_equiv e'.symm).mp inj
          ⟨e.symm ⟨_, hx⟩, Subtype.coe_prop _, hxl⟩
      have hk := congrArg Subtype.val hk; simp only at hk
      rw [← hk]; exact mono (Fin.zero_le _)
    | succ k ih =>
      intro f first mono next inj
      let z := e ⟨_, f.last.property.1⟩
      by_cases hzf : z = f.first.val
      · subst first
        refine le_of_le_of_eq (mono (Fin.zero_le _)) (congrArg _ ?_) (b := α.lab f.last.val)
        have : f.last.val = (Subtype.mk _ f.last.property.1).val := rfl; rw [this]
        refine congrArg _ ((e.symm_apply_apply _).symm.trans ?_)
        refine congrArg _ (Subtype.ext ?_); simp only; rw [← hzf]
      · have hzl : α.rel.lev z = i := by
          refine ((Set.ext_iff.mp (permute_le_lev_nodes hle) _).mpr ⟨z.property, ?_⟩).2
          exact ((Lpo.permute_lev e f.last.property.1).symm.trans (f.last.property.2))
        have hz : ∀ j, f j ≠ ⟨z, z.property, hzl⟩ := by
          intro j hj; by_cases h0 : j = 0
          · subst h0; refine hzf (Eq.trans ?_ (congrArg _ hj).symm); simp only
          · have hj1 : 1 ≤ j.val := by
              refine (Nat.one_le_iff_ne_zero.mpr ?_); intro h; exact h0 (Fin.val_inj.mp h)
            have := next ⟨j.val - 1, by {
              refine Nat.pred_lt_pred ?_ ?_
              · simp only [Nat.sub_eq, tsub_zero, ne_eq]; intro h; exact h0 (Fin.val_inj.mp h)
              · simp only [Nat.sub_eq, tsub_zero]; refine lt_of_lt_of_eq j.isLt ?_
                refine Nat.sub_add_cancel ?_
                refine (Nat.le_of_lt_succ (lt_of_le_of_lt hj1 j.isLt)).trans ?_
                simp only [tsub_le_iff_right, le_add_iff_nonneg_right, zero_le]
            }⟩; simp only [Fin.eta] at this
            have hj' {h} : ⟨j.val - 1 + 1, h⟩ = j := by
              ext; simp; refine Nat.sub_add_cancel hj1
            rw [hj', hj] at this; simp only [z] at this
            have := Subtype.val_inj.mpr (e.injective (Subtype.ext this)); simp only [FinChain.last, Fin.last] at this
            have := Fin.val_inj.mpr (inj (Subtype.ext this)); simp only at this
            refine ne_of_lt (Nat.succ_lt_succ_iff.mp ?_) this.symm
            refine lt_of_eq_of_lt ?_ j.isLt; simp only [Nat.succ_eq_add_one]; refine Nat.sub_add_cancel hj1
        refine
          ih
            (fun j ↦ if hj : j.val < n - (k + 1) - 1 + 1 then f ⟨j.val, hj⟩ else ⟨z, z.property, hzl⟩)
            ?_ ?_ ?_ ?_
        · refine (congrArg _ ?_).trans first
          simp only [FinChain.first, lt_add_iff_pos_left, add_pos_iff, tsub_pos_iff_lt,
            Nat.lt_one_iff, pos_of_gt, or_true, ↓reduceDIte, Fin.zero_eta]
        · intro i j hle; simp only [z]
          by_cases hj : j.val < n - (k + 1) - 1 + 1
          · rw [dif_pos hj];
            have hi : i.val < n - (k + 1) - 1 + 1 :=
              lt_of_le_of_lt (Fin.val_fin_le.mpr hle) hj
            rw [dif_pos hi]; exact mono hle
          · rw [dif_neg hj]
            by_cases hi : i.val < n - (k + 1) - 1 + 1
            · rw [dif_pos hi]; refine le_trans ?_ (hlab f.last.property.1)
              exact mono (Fin.le_last _)
            · rw [dif_neg hi]
        · intro j; simp only [add_lt_add_iff_right, z]
          by_cases hj : j.val < n - (k + 1) - 1
          · rw [dif_pos hj]
            refine (next ⟨j.val, hj⟩).trans ?_
            refine congrArg _ (congrArg _ (Subtype.ext ?_)); simp only
            refine congrArg _ (Eq.trans ?_ (dif_pos ?_).symm)
            · rfl
            · exact hj.trans (Nat.lt_succ_self _)
          · rw [dif_neg hj]; simp only [z]
            refine congrArg _ (congrArg _ (Subtype.ext ?_)); simp only
            have : j.val ≤ n - (k + 1) - 1 := by
              refine le_of_le_of_eq (Nat.le_pred_of_lt j.isLt) ?_
              refine congrArg Nat.pred ?_; simp only [Nat.sub_eq, tsub_zero]
              exact (Nat.sub_add_eq _ _ _).symm
            refine congrArg _ (Eq.trans ?_ (dif_pos ?_).symm)
            · refine congrArg f (Fin.val_inj.mp ?_); simp only [Fin.last]
              exact (eq_of_le_of_not_lt this hj).symm
            · refine Nat.lt_of_le_pred ?_ ?_
              · exact Nat.zero_lt_succ _
              · exact this
        · intro i j hij; simp only at hij
          by_cases hi : i.val < n - (k + 1) - 1 + 1
          · rw [dif_pos hi] at hij
            by_cases hj : j.val < n - (k + 1) - 1 + 1
            · rw [dif_pos hj] at hij
              have := Fin.val_inj.mpr (inj hij); simp only at this
              exact Fin.val_inj.mp this
            · rw [dif_neg hj] at hij; exfalso; exact hz ⟨i.val, hi⟩ hij
          · rw [dif_neg hi] at hij
            by_cases hj : j.val < n - (k + 1) - 1 + 1
            · rw [dif_pos hj] at hij; exfalso; exact hz ⟨j.val, hj⟩ hij.symm
            · refine Fin.val_inj.mp ?_
              refine Eq.trans ?_ (Eq.symm ?_) (b := n - k - 1) <;>
                refine le_antisymm (Nat.le_of_lt_succ ?_) ?_
              · exact i.isLt
              · exact le_of_eq_of_le (Nat.sub_add_eq _ _ _).symm (le_trans le_tsub_add (le_of_not_gt hi))
              · exact j.isLt
              · exact le_of_eq_of_le (Nat.sub_add_eq _ _ _).symm (le_trans le_tsub_add (le_of_not_gt hj))
  refine build_chain n (fun _ ↦ ⟨x, hx, hlev⟩) rfl ?_ ?_ ?_
  · intro _ _ _; exact le_refl _
  · intro i; simp only [tsub_self, zero_le, Nat.sub_eq_zero_of_le] at i; exact Fin.elim0 i
  · intro i j _; ext;
    have hi := i.isLt; have hj := j.isLt;
    simp only [tsub_self, zero_le, Nat.sub_eq_zero_of_le, zero_add, Nat.lt_one_iff] at hi hj
    rw [hi, hj]

lemma permute_le_self {l : Type} [PartialOrder l] [OrderBot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} (hle : α.permute e ≤ α) : α.permute e = α := by
  have hn : α.val.nodes = (α.permute e).val.nodes :=
    permute_le_self_nodes hle
  simp [Lpo.permute] at hn; subst hn
  ext1
  · simp only [Lpo.permute, Lpo.nodes]
  · ext x y; constructor <;> intro hrel
    · exact le_rel hle hrel
    · obtain ⟨hx, hy⟩ := α.property.rel_dom hrel
      exact (hle.rel _ hx _ hy).mpr hrel
  · ext x; by_cases hx : x ∈ α.val.nodes
    · refine le_antisymm (hle.lab x) ?_
      exact permute_le_self_lab hle hx
    · conv => rhs; exact α.property.lab_dom _ hx
      exact (α.permute e).property.lab_dom _ hx
  · ext1 x; by_cases hx : x ∈ α.val.nodes
    · exact hle.form _ hx
    · ext v; constructor; all_goals {
        intro hform; exfalso
        refine ((Subtype.property _ : is_valid_lpo _).form_dom x).mp.mt ?_ ⟨_, hform⟩
        exact hx
      }

instance {l : Type} [PartialOrder l] [OrderBot l] : PartialOrder (Pom l) where
  le_antisymm p q hpq hqp := by
    obtain ⟨α, rfl, β, rfl, hle⟩ := hpq
    obtain ⟨β', heq, hle'⟩ := Pom.ge_lpo hqp
    obtain ⟨e, he⟩ := Quotient.exact heq
    rw [← he] at hle'
    have hp := permute_le_self (hle'.trans hle)
    rw [le_antisymm hle (le_of_eq_of_le hp.symm hle')]
