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


lemma permute_le_self_nodes_fin {l : Type} [PartialOrder l] [OrderBot l] {α : Lpofin l} {X : Set Node}
    {e : α.nodes ≃ X} (h : α.permute e ≤ α) : α.nodes = (α.permute e).nodes := by
  symm; refine α.property.eq_of_subset_of_card_le ?_ ?_
  · exact h.nodes
  · obtain ⟨n, ⟨e'⟩⟩ := finite_iff_exists_equiv_fin.mp α.property
    refine le_of_eq (Eq.trans (b := n) ?_ (Eq.symm ?_)) <;>
      refine Nat.card_eq_of_equiv_fin ?_
    · exact e'
    · simp only [Lpofin.permute, Lpo.permute, Lpofin.nodes, Lpo.nodes]
      exact e.symm.trans e'

lemma permute_le_lev_nodes {l : Type} [LE l] [Bot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} {n : ℕ} (h : α.permute e ≤ α) :
    { x ∈ α.nodes | α.rel.lev x = n} =
    { x ∈ (α.permute e).nodes | (α.permute e).rel.lev x = n } := by sorry
  -- induction n with
  -- | zero => sorry
  -- | succ k ih =>

  -- obtain ⟨k, ⟨e'⟩⟩ := (α.property.rel.fin_lev n).exists_equiv_fin
  -- refine Set.symmDiff_eq_empty.mp ?_


  -- induction k with

  -- let e' := Lpo.perm_subset e fun x (hx : x ∈ α.nodes ∧ α.rel.lev x = n) ↦ hx.1
  -- symm; refine Set.Finite.eq_of_subset_of_card_le ?_ ?_ ?_
  -- · exact α.property.rel.fin_lev n
  -- · intro x ⟨hx, hlev⟩; refine ⟨h.nodes hx, Eq.trans ?_ hlev⟩
  --   have hh := Lpo.permute_lev e (h.nodes hx)

  -- ·


lemma permute_le_self_nodes {l : Type} [DCPO l] [OrderBot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} (h : α.permute e ≤ α) : α.nodes = (α.permute e).nodes := by
  -- have {β : Lpo l} : β.nodes = ⋃ n : ℕ, { x ∈ β.nodes | β.rel.lev x = n } := by
  --   ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left, iff_self_and]
  --   exact lev_finite
  -- refine this.trans (this.trans ?_).symm; refine iSup_congr fun i ↦ ?_
  -- refine Set.Finite.eq_of_subset_of_card_le ?_ ?_ ?_
  -- · exact α.property.rel.fin_lev i
  -- · intro x ⟨hx, hlev⟩; refine ⟨h.nodes hx, Eq.trans ?_ hlev⟩
  --   have hh := Lpo.permute_lev e (h.nodes hx)
  conv => lhs; exact congrArg Lpo.nodes (Lpo.trunc_chain_sup _)
  conv => rhs; exact congrArg Lpo.nodes (Lpo.trunc_chain_sup _)
  rw [Lpo.ωSup_nodes, Lpo.ωSup_nodes]; refine iSup_congr fun i ↦ ?_
  simp only [Lpo.trunc_chain, ← Lpo.trunc_permute]
  refine permute_le_self_nodes_fin ?_
  refine le_of_eq_of_le ?_ (Lpo.trunc_mono h (le_refl i))
  exact Subtype.ext Lpo.trunc_permute

lemma permute_le_self {l : Type} [DCPO l] [OrderBot l] {α : Lpo l} {X : Set Node}
    {e : α.nodes ≃ X} (hle : α.permute e ≤ α) : α.permute e = α := by
  have hn : α.val.nodes = (α.permute e).val.nodes :=
    permute_le_self_nodes hle
  ext1
  · exact hn.symm
  · ext x y; constructor <;> intro hrel
    · exact le_rel hle hrel
    · obtain ⟨hx, hy⟩ := α.property.rel_dom hrel
      rw [hn] at *; exact (hle.rel _ hx _ hy).mpr hrel
  · ext x; by_cases hx : x ∈ α.val.nodes
    · refine le_antisymm (hle.lab x) ?_
      obtain ⟨i, hlev⟩ := lev_finite hx
      obtain ⟨n, ⟨e'⟩⟩ := (α.property.rel.fin_lev i).exists_equiv_fin
      -- have : ∃ k : ℕ, ∃ c : FinChain k Node,
      --   ∀ j : Fin k, α.lab (c j)
      have hlab := hle.lab (e ⟨_, hx⟩)
      simp only [Lpo.lab, Lpo.permute, Subtype.exists, exists_and_right, Subtype.coe_prop,
        ↓reduceDIte, Subtype.coe_eta, Equiv.symm_apply_apply] at hlab
      refine hlab.trans ?_
      simp [Lpo.permute, Lpo.lab]
      sorry
    · conv => rhs; exact α.property.lab_dom _ hx
      rw [hn] at hx; exact (α.permute e).property.lab_dom _ hx
  · ext1 x; by_cases hx : x ∈ α.val.nodes
    · rw [hn] at hx; exact hle.form _ hx
    · ext v; constructor; all_goals {
        intro hform; exfalso
        refine ((Subtype.property _ : is_valid_lpo _).form_dom x).mp.mt ?_ ⟨_, hform⟩
        try exact hx
        try rw [hn] at hx; exact hx
      }

instance {l : Type} [DCPO l] [OrderBot l] : PartialOrder (Pom l) where
  le_antisymm p q hpq hqp := by
    obtain ⟨α, rfl, β, rfl, hle⟩ := hpq
    obtain ⟨β', heq, hle'⟩ := Pom.ge_lpo hqp
    obtain ⟨e, he⟩ := Quotient.exact heq
    rw [← he] at hle'
    have hp := permute_le_self (hle'.trans hle)
    rw [le_antisymm hle (le_of_eq_of_le hp.symm hle')]
