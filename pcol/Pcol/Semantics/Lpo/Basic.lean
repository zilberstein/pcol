import Init.Prelude
import Mathlib.Data.ENat.Basic
import Mathlib.Data.ENat.Defs
import Mathlib.Data.ENat.Lattice
import Mathlib.Data.Finite.Card
import Mathlib.Data.Finite.Defs
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Rel
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.SetNotation
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic.Linarith

def Node := ℕ
instance : Inhabited Node where
  default := (0 : ℕ)

instance : DecidableEq Node := instDecidableEqNat

def Form (α : Type) := Set α → Prop

@[ext]
lemma form_ext {α : Type} {φ ψ : Form α} (h : ∀ x, φ x = ψ x) : φ = ψ := funext h

namespace Form

variable {α : Type}

def true : Form α := fun _ => True
def false: Form α := fun _ => False
def and (p : Form α) (q : Form α) : Form α := fun v => p v ∧ q v
def or (p : Form α) (q : Form α) : Form α := fun v => p v ∨ q v
def not (p : Form α) : Form α := fun v => ¬(p v)
def literal (x : α) : Form α := fun v => x ∈ v

def sOr {β : Type} (s : Set β) (p : β → Form α) : Form α :=
  fun v ↦ ∃ x ∈ s, p x v
def sAnd {β : Type} (s : Set β) (p : β → Form α) : Form α :=
  fun v ↦ ∀ x ∈ s, p x v

def sat (p : Form α) : Prop := ∃ v, p v

instance : LE (Form α) where
  le φ ψ := ∀ v, φ v → ψ v

instance : Preorder (Form α) where
  le_refl φ v h := h
  le_trans φ ψ ξ h₁ h₂ v hφ := h₂ v (h₁ v hφ)

instance : PartialOrder (Form α) where
  le_antisymm φ ψ h₁ h₂ := by ext v; exact ⟨h₁ v, h₂ v⟩

lemma mt {p q : Form α} (h : p ≤ q) : q.not ≤ p.not := by
  intro v hqn hp; exact hqn (h v hp)

def free [DecidableEq α] (p : Form α) (x : α) : Prop :=
  ∀ v, p v ↔ p (fun y => if x = y then ¬(v y) else v y)

def vars (p : Form Node) : Set Node :=
  { x | ¬ p.free x }

lemma sat_on_vars_fin {p : Form Node} {s : Set Node}
    (hs : ∀ x ∈ s, p.free x) (hf : s.Finite) :
    ∀ v₁ v₂, (∀ x ∉ s, x ∈ v₁ ↔ x ∈ v₂) → (p v₁ ↔ p v₂) := by
  revert hs; refine hf.induction_on s ?_ ?_
  · intro _ v₁ v₂ h
    have heq : v₁ = v₂ := by ext x; exact h _ id
    subst heq; rfl
  · intro x t hx ht ih hins v₁ v₂ h
    by_cases hv : x ∈ v₁ ↔ x ∈ v₂
    · refine ih ?_ _ _ ?_
      · intro y hy; exact hins _ (Set.mem_insert_of_mem _ hy)
      · intro y hy; by_cases hxy : x = y
        · subst hxy; exact hv
        · refine h _ (Set.eq_or_mem_of_mem_insert.mt (not_or.mpr ⟨Ne.symm hxy, hy⟩))
    · refine (hins _ (Set.mem_insert _ _) v₁).trans ?_
      refine ih ?_ _ _ ?_
      · intro y hy; exact hins _ (Set.mem_insert_of_mem _ hy)
      · intro y hy; by_cases hxy : x = y <;> simp only [Membership.mem, hxy, Set.Mem, ↓reduceIte]
        · subst hxy; exact not_iff.mp hv
        · refine h _ (Set.eq_or_mem_of_mem_insert.mt (not_or.mpr ⟨Ne.symm hxy, hy⟩))

lemma sat_if_vars_nonempty {p : Form Node} (h : p.vars.Nonempty) : p.sat := by
  simp only [vars, free, not_forall] at h
  obtain ⟨x, v, hform⟩ := h
  by_cases h : p v
  · exact ⟨v, h⟩
  · exact ⟨_, (not_iff.mp hform).mp h⟩

end Form

def FinChain (n : ℕ) (α : Type) := Fin (n + 1) → α

namespace FinChain

def first {n : ℕ} {α : Type} (c : FinChain n α) : α :=
  c ⟨0, by linarith⟩

def last {n : ℕ} {α : Type} (c : FinChain n α) : α :=
  c (Fin.last n)

def snd_to_last {n : ℕ} {α : Type} (c : FinChain (n + 1) α) : α :=
  c ⟨n, by linarith⟩

lemma first_neq_last {n : ℕ} {α : Type} (c : FinChain n α) (hne : c.first ≠ c.last) : n > 0 := by
  have h := fun c ↦ hne (congrArg _ (Fin.val_inj.mp c))
  refine Ne.bot_lt (Ne.symm h)

end FinChain

namespace Rel

def roots {a : Type} (ord : Rel a a) : Set a := { x : a | ∀ y, ¬(ord y x) }

def is_succ_chain {α : Type} {n : ℕ} (ord : Rel α α) (c : FinChain n α) : Prop :=
  ∀ k : Fin n, by
    refine ord (c ⟨k, ?_⟩) (c ⟨k + 1, ?_⟩)
    · refine lt_of_lt_of_le k.isLt ?_; simp
    · refine lt_of_lt_of_le (add_lt_add_of_lt_of_le k.isLt (le_refl _)) (le_refl _)

def is_down_closed (ord : Rel Node Node) (X : Set Node) : Prop :=
  ∀ x ∈ X, ∀ y, ord y x → y ∈ X

def IsUpClosed (ord : Rel Node Node) (X : Set Node) : Prop :=
  ∀ x ∈ X, ∀ y, ord x y → y ∈ X

def up_closure (ord : Rel Node Node) (X : Set Node) : Set Node :=
  { x | ∃ y ∈ X, ord y x }

noncomputable def lev {a : Type} (ord : Rel a a) (x : a) : ENat :=
  sSup { n | ∃ k : ℕ, n = ↑k ∧ ∃ c : FinChain k a, ord.is_succ_chain c ∧ c.last = x }

def FinitelyPreceded {α : Type} (ord : Rel α α) : Prop :=
  ∀ x : α, { y | ord y x }.Finite

structure IsCausalityRel {α : Type} (ord : Rel α α) (s : Set α) : Prop where
  -- ord is a strict partial order
  trans : Transitive ord
  antisymm : AntiSymmetric ord
  irrefl : Irreflexive ord
  -- ord is finitely preceeded
  fin_prec : FinitelyPreceded ord
  -- each level is finite
  fin_lev: ∀ n : ℕ, { x | x ∈ s ∧ ord.lev x = n}.Finite
  -- ord is single-rooted
  single_rooted : ∃ x ∈ s, ∀ y ∈ s, x ≠ y → ord x y

end Rel

structure Lpo_base (l : Type) where
  nodes : Set Node
  rel : Rel Node Node
  lab : Node → l
  form : Node → Form Node
attribute [ext] Lpo_base

structure is_valid_lpo {l : Type} [Bot l] (a : Lpo_base l) : Prop where
  rel_dom : ∀ {x y}, a.rel x y → x ∈ a.nodes ∧ y ∈ a.nodes
  lab_dom : ∀ x ∉ a.nodes, a.lab x = ⊥
  -- The order is valid
  rel : a.rel.IsCausalityRel a.nodes
  -- Bot nodes have no successors
  bot : ∀ x, a.lab x = ⊥ → ∀ y, ¬(a.rel x y)
  -- Formulae
  form_dom : ∀ x, (a.form x).sat ↔ x ∈ a.nodes
  form : ∀ x ∈ a.nodes, (∀ y ∈ (a.form x).vars, a.rel y x) ∧
          ∀ z, a.rel x z → a.form z ≤ a.form x


def Lpo (l : Type) [Bot l] := { α : Lpo_base l // is_valid_lpo α }

namespace Lpo

def nodes {l : Type} [Bot l] (a : Lpo l) : Set Node := a.val.nodes
def rel {l : Type} [Bot l] (a : Lpo l) : Rel Node Node := a.val.rel
def lab {l : Type} [Bot l] (a : Lpo l) : Node → l := a.val.lab
def form {l : Type} [Bot l] (a : Lpo l) : Node → Form Node := a.val.form

def bots {l : Type} [Bot l] (a : Lpo l) : Set Node := { x | x ∈ a.nodes ∧ a.lab x = ⊥}

lemma not_in_dom_not_rel {l : Type} [Bot l] (a : Lpo l) (x y : Node)
  (h : x ∉ a.nodes ∨ y ∉ a.nodes) : ¬(a.rel x y) := by {
  intro hrel; have hc := a.property.rel_dom hrel
  cases h with
  | inl hx => exact hx hc.1
  | inr hy => exact hy hc.2
}

def singleton {l : Type} [Bot l] (x : Node) (ℓ : l) : Lpo l :=
  Subtype.mk {
    nodes := {x}
    rel _ _ := False
    lab y := if x = y then ℓ else ⊥
    form y := if x = y then Form.true else Form.false
  } (by {
    constructor <;> try simp
    · intro y h hc; rw [hc] at h; contradiction
    · constructor
      · intro _ _ hxy _; contradiction
      · intro _ _ hc; contradiction
      · intro _ hc; contradiction
      · intro y; simp only [Set.setOf_false, Set.finite_empty]
      · intro _; exact (Set.finite_singleton x).subset fun y ⟨hy, _⟩ ↦ hy
      · refine ⟨x, Set.mem_singleton _, ?_⟩; rintro y rfl hc; exact hc rfl
    · intro y; constructor
      · rintro ⟨v, h⟩; by_cases heq : x = y
        · exact Eq.symm heq
        · rw [ite_cond_eq_false _ _ (eq_false heq)] at h
          simp [Form.false] at h
      · intro heq; use ∅
        rw [ite_cond_eq_true _ _ (eq_true (Eq.symm heq))]; simp [Form.true]
    · intro y; simp only [Form.vars, Form.free, Form.true, implies_true, not_true_eq_false,
        Set.setOf_false, Set.mem_empty_iff_false, not_false_eq_true]
  })

end Lpo

@[ext]
lemma lpo_ext {l : Type} [Bot l] {a b : Lpo l}
    (hnodes : a.nodes = b.nodes)
    (hrel : a.rel = b.rel)
    (hlab : a.lab = b.lab)
    (hform : a.form = b.form) : a = b := by
  refine Subtype.ext ?_; ext
  · simp [Lpo.nodes] at hnodes; rw [hnodes]
  · unfold Lpo.rel at hrel; rw [hrel]
  · unfold Lpo.lab at hlab; rw [hlab]
  · unfold Lpo.form at hform; rw [hform]

lemma lpo_eq_iff {l : Type} [Bot l] {a b : Lpo l} :
  a = b ↔
    a.nodes = b.nodes ∧
    a.rel = b.rel ∧
    a.lab = b.lab ∧
    a.form = b.form := by {
  constructor
  · intro heq; rw [heq]; use rfl
  · intro ⟨heq, hrel, hlab, hform⟩; exact lpo_ext heq hrel hlab hform
}

lemma form_eq_false {l : Type} [Bot l] {α : Lpo l} {x : Node} :
    x ∉ α.nodes ↔ α.form x = Form.false := by
  constructor
  · intro hx; ext v; refine ⟨?_, False.elim⟩
    intro hform; have h := (α.property.form_dom _).mp.mt hx
    simp only [Form.sat, not_exists] at h
    exact h _ hform
  · intro hform; refine (α.property.form_dom x).mpr.mt ?_
    unfold Lpo.form at hform; rw [hform]
    simp only [Form.sat, Form.false, exists_const, not_false_eq_true]

lemma lev_zero {l : Type} [Bot l] {α : Lpo l} {x : Node} (hx : x ∈ α.nodes)
    (hlev : α.rel.lev x = 0) (y : Node) (hy : y ∈ α.nodes) (hneq : x ≠ y) :
    α.rel x y := by
  obtain ⟨z, hz, hroot⟩ := α.property.rel.single_rooted
  by_cases heq : x = z
  · subst heq; exact hroot _ hy hneq
  · exfalso
    have hzx := hroot _ hx (Ne.symm heq)
    let c : FinChain 1 Node := fun k ↦ if k = 0 then z else x
    have hc : α.rel.is_succ_chain c := by
      intro k; have hk := Fin.eq_zero k; subst hk
      simp only [Nat.reduceAdd, Fin.isValue, Fin.val_eq_zero, Fin.zero_eta, ↓reduceIte, zero_add,
        Fin.mk_one, one_ne_zero, c]; exact hzx
    have hl : c.last = x := by simp [c, FinChain.last]
    have hzero := sSup_eq_bot.mp hlev 1 ⟨1, rfl, c, hc, hl⟩
    exact one_ne_zero hzero

lemma succ_chain_mono {l : Type} [Bot l] {α : Lpo l} {n : ℕ} (c : FinChain n Node)
    (h : α.rel.is_succ_chain c) {i j : Fin (n + 1)} (hlt : i < j) :
    α.rel (c i) (c j) := by
  generalize hk : j.val - i.val = k; revert i j hk; induction k with
  | zero =>
    intro i j hlt hk; exfalso; refine ne_of_lt hlt ?_
    refine le_antisymm (le_of_lt hlt) ?_; exact Nat.sub_eq_zero_iff_le.mp hk
  | succ k ih =>
    intro i j hlt hk
    let i' : Fin n := by
      refine ⟨i.val, ?_⟩; refine lt_of_lt_of_le (Fin.val_fin_lt.mp hlt) ?_
      exact Nat.le_of_lt_succ j.isLt
    cases k with
    | zero =>
      have : j = ⟨i.val + 1, lt_of_le_of_lt (Nat.succ_le_of_lt hlt) j.isLt⟩ := by
        ext; refine (Nat.sub_add_cancel (le_of_lt hlt)).symm.trans ?_
        rw [hk]; linarith
      rw [this]; exact h i'
    | succ k =>
      refine α.property.rel.trans (h i') ?_
      refine ih (Fin.val_fin_lt.mp ?_) ?_
      · simp only [i']; refine lt_of_lt_of_eq ?_ (Nat.sub_add_cancel (le_of_lt hlt))
        rw [hk]; linarith
      · simp only [i']; rw [Nat.sub_add_eq, hk, add_tsub_cancel_right]

lemma succ_chain_inj {l : Type} [Bot l] {α : Lpo l} {n : ℕ} {c : FinChain n Node}
    (hc : α.rel.is_succ_chain c) : Function.Injective c := by
  intro i j heq; by_contra hcn
  refine α.property.rel.irrefl (c i) ?_
  rcases ne_iff_lt_or_gt.mp hcn with hlt | hlt
  all_goals {
    have hrel := succ_chain_mono c hc hlt
    rw [← heq] at hrel; exact hrel
  }

lemma lev_root {l : Type} [Bot l] {α : Lpo l} {x : Node} (hx : x ∈ α.nodes)
    (hroot : ∀ y ∈ α.nodes, x ≠ y → α.rel x y) :
    α.rel.lev x = 0 := by
  refine eq_bot_iff.mpr (sSup_le ?_)
  rintro _ ⟨k, rfl, c, hc, rfl⟩; simp only [bot_eq_zero', nonpos_iff_eq_zero, Nat.cast_eq_zero]
  by_contra h
  apply bot_lt_iff_ne_bot.mpr at h
  have hne : ⟨0, by linarith⟩ < Fin.last k := Fin.lt_def.mpr h
  have hle := succ_chain_mono c hc hne
  have h0 := (α.property.rel_dom hle).1
  have hne' := (succ_chain_inj hc).ne (ne_of_lt hne)
  refine hne' (α.property.rel.antisymm hle ?_)
  exact hroot _ h0 (Ne.symm hne')

lemma lev_finite {l : Type} [Bot l] {α : Lpo l} {x : Node} (hx : x ∈ α.nodes) :
    ∃ n : ℕ, α.rel.lev x = n := by
  refine (fun hnt ↦ let ⟨n, h⟩ := ENat.ne_top_iff_exists.mp hnt; ⟨n, h.symm⟩) ?_
  obtain ⟨n, hfin⟩ := (α.property.rel.fin_prec x).exists_encard_eq_coe
  refine ne_top_of_le_ne_top (ENat.coe_ne_top n) ?_
  refine sSup_le ?_; rintro _ ⟨k, rfl, c, hc, rfl⟩;
  have hcard : { x | ∃ k', k' < k ∧ x = c k'}.encard = ↑k := by
    refine Eq.trans (Set.encard_congr (Equiv.trans ?_ (Equiv.Set.univ _).symm))
      ((Set.encard_univ _).trans (ENat.card_eq_coe_fintype_card.trans (congrArg _ (Fintype.card_fin k))))
    rw [Set.coe_setOf]
    have h x (hx : ∃ k' < k, x = c ↑k') : ∃ (y : Fin k), c y = x := by
      obtain ⟨k', hk', rfl⟩ := hx; exact ⟨⟨k', hk'⟩, rfl⟩
    choose f hf using h
    refine ⟨fun x ↦ f x.val x.property,
            fun k' ↦ ⟨c k', k', k'.isLt, rfl⟩, ?_, ?_⟩
    · rintro ⟨y, hy⟩; have h := hf y hy
      simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq]
      simp only [Fin.coe_eq_castSucc, Subtype.mk.injEq] at h
      exact h
    · intro k'; simp only [Fin.coe_eq_castSucc]
      have h := succ_chain_inj hc (hf (c k') ⟨k'.val, k'.isLt, rfl⟩)
      simp only [Fin.coe_eq_castSucc, Fin.castSucc_inj] at h; exact h
  rw [← hfin, ← hcard]
  refine Set.encard_mono ?_; rintro x ⟨k', hk, rfl⟩
  refine succ_chain_mono c hc (Fin.mk_lt_mk.mpr ?_)
  refine lt_of_eq_of_lt (Nat.mod_succ_eq_iff_lt.mpr ?_) hk
  linarith

lemma lev_finite_exists_finchain {l : Type} [Bot l] {α : Lpo l} {n : ℕ} {x : Node}
    (hlev : α.rel.lev x = n) :
    ∃ c : FinChain n Node, α.rel.is_succ_chain c ∧ c.last = x := by
  simp only [Rel.lev, Set.mem_setOf_eq] at hlev
  have _ :
      Nonempty
        ↑{n : ENat | ∃ k : ℕ, n = ↑k ∧ ∃ c : FinChain k Node, α.rel.is_succ_chain c ∧ c.last = x} :=
    ⟨0, 0, rfl, fun _ ↦ x, finZeroElim, rfl⟩
  have hsup := ENat.sSup_mem_of_nonempty_of_lt_top (lt_of_eq_of_lt hlev (ENat.coe_lt_top _))
  rw [hlev] at hsup ; simp only [Set.mem_setOf_eq, Nat.cast_inj, exists_eq_left'] at hsup
  exact hsup

lemma lev_mono {l : Type} [Bot l] {α : Lpo l} {x y : Node} (h : α.rel x y) :
    α.rel.lev x < α.rel.lev y := by
  have hx := (α.property.rel_dom h).1
  obtain ⟨n, hlev⟩ := lev_finite hx
  obtain ⟨c, hc, hl⟩ := lev_finite_exists_finchain hlev
  let c' : FinChain (n + 1) Node := fun k ↦
    if hk : k.val < n + 1 then c ⟨k.val, hk⟩ else y
  rw [hlev]; refine lt_of_lt_of_le (b := ↑(n + 1)) ?_ ?_
  · refine ENat.coe_lt_coe.mpr ?_; linarith
  · refine le_sSup ?_
    simp only [Nat.cast_add, Nat.cast_one, Set.mem_setOf_eq]
    refine ⟨n + 1, rfl, c', ?_, ?_⟩
    · intro k; by_cases hk : k.val < n <;>
      simp only [Fin.is_lt, ↓reduceDIte, Fin.eta, add_lt_add_iff_right, hk, c']
      · exact hc ⟨k.val, hk⟩
      · subst hl; rcases k with ⟨k, hlt⟩
        have : k = n := by
          refine le_antisymm ?_ (not_lt.mp hk)
          linarith
        subst this; refine (congrArg₂ _ ?_ rfl).mpr h; rfl
    · simp only [FinChain.last, Fin.val_last, lt_self_iff_false, ↓reduceDIte, c']

-- The proof is almost done, except for some annoying arithmetic with Nats
lemma exists_node_lt_lev {l : Type} [Bot l] {α : Lpo l} {n : ℕ} {x : Node}
   (hx : x ∈ α.nodes) (hlt : n < α.rel.lev x) : ∃ y, α.rel.lev y = n ∧ α.rel y x := by
  obtain ⟨m, hlev⟩ := lev_finite hx
  obtain ⟨c, hc, rfl⟩ := lev_finite_exists_finchain hlev
  have hnm : n < m := ENat.coe_lt_coe.mp (lt_of_lt_of_eq hlt hlev)
  refine ⟨c ⟨n, ?_⟩, ?_, ?_⟩
  · exact hnm.trans (Nat.lt_succ_self _)
  · refine le_antisymm ?_ ?_
    -- Proof by contradiction: show that if the nth element of the chain has level greater than
    -- n, then the level of x must be greater than m
    · by_contra h; apply not_le.mp at h
      let n' : Fin (m + 1) := ⟨n, by linarith⟩
      have hn := (α.property.rel_dom (hc ⟨n, hnm⟩)).1
      obtain ⟨n', hn'⟩ := lev_finite hn
      have hnn : n < n' := ENat.coe_lt_coe.mp (lt_of_lt_of_eq h hn')
      have hnle : ¬ (n' + m - n ≤ m) := by
        refine not_le_of_lt ?_; rw [add_comm]
        refine lt_of_lt_of_eq ?_ (Nat.add_sub_assoc ?_ _).symm
        · exact Nat.lt_add_of_pos_right (tsub_pos_iff_lt.mpr hnn)
        · exact le_of_lt hnn
      apply hnle; refine ENat.coe_le_coe.mp ?_; simp only [ENat.coe_sub, Nat.cast_add]
      nth_rw 2 [← hlev]; refine le_sSup ?_; simp only [Set.mem_setOf_eq]
      obtain ⟨cn, hcn, hl'⟩ := lev_finite_exists_finchain hn'
      let c' : FinChain (n' + m - n) Node := fun k ↦
        if h : k.val < n' then
          cn ⟨k.val, by linarith⟩
        else
          c ⟨k.val - n' + n, by sorry ⟩
          --   refine lt_trans (Nat.add_lt_add (Nat.sub_lt_sub_right ?_ k.isLt) hnn) ?_
          --   · exact not_lt.mp h
          --   · rw [Nat.sub_add_cancel]
          --     · nth_rw 2 [add_comm]
          --       refine (Nat.add_lt_add_right (Nat.sub_lt_sub_right ?_ (Nat.add_lt_add_left hnn _)) _).trans ?_
          --       rw [Nat.sub_add_cancel]

          -- ⟩
          --   refine lt_trans ?_ ?_ (b := ((n' + m - n + 1) + n) - n')
          --   · refine Nat.sub_lt_sub_right ?_ ?_
          --     · refine Nat.le_add_right_of_le (not_lt.mp h)
          -- ⟩
      refine ⟨n' + m - n, rfl, c', ?_, ?_⟩
      · intro k'; by_cases hk : k'.val < n'
        · simp [c', hk]; by_cases hk' : k'.val + 1 < n' <;> simp only [hk', ↓reduceIte, c']
          · exact hcn ⟨k', hk⟩
          · have : k'.val + 1 = n' := by grind
            refine (congrArg₂ _ rfl ?_).mp (hcn ⟨k', hk⟩)
            · simp only [c']; refine (Eq.trans ?_ hl').trans ?_
              · refine congrArg _ ?_; ext; simp only [Fin.val_last]; exact this
              · refine congrArg _ ?_; ext; simp only; rw [this]
                simp only [tsub_self, zero_add]
        · have : ¬ (k' + 1 < n') := by linarith
          simp [c', hk, this]
          refine (congrArg₂ _ rfl ?_).mp  (hc ⟨k'.val - n' + n, ?_⟩)
          · refine congrArg _ ?_; ext; simp only [c']
            sorry
          · sorry
      · have :  ¬ (n' + m - n < n') := by sorry
        simp [FinChain.last, dite_eq_ite, Fin.val_last, this, ↓reduceIte, c']
        refine congrArg _ ?_; ext; simp only [Fin.val_last]
        sorry
    · refine le_sSup ?_; simp only [Set.mem_setOf_eq, Nat.cast_inj, exists_eq_left']
      refine ⟨fun k ↦ c ⟨k.val, k.isLt.trans ?_⟩, ?_, rfl⟩
      · linarith
      · intro k; exact hc ⟨k, k.isLt.trans hnm⟩
  · refine succ_chain_mono c hc (Fin.val_fin_lt.mp ?_); simp only [Fin.val_last]
    exact ENat.coe_lt_coe.mp (lt_of_lt_of_eq hlt hlev)

lemma form_root_true {l : Type} [Bot l] {α : Lpo l} {x : Node} (hx : x ∈ α.nodes)
    (hr : ∀ y ∈ α.nodes, x ≠ y → α.rel x y) :
    α.form x = Form.true := by
  ext v; refine ⟨fun _ ↦ True.intro, fun _ ↦ ?_⟩
  have hvars : (α.form x).vars = ∅ := by
    ext y; refine ⟨fun hc ↦ ?_, fun hc ↦ False.elim hc⟩
    apply (α.property.form _ hx).1 at hc
    by_cases h : x = y
    · subst h; exact α.property.rel.irrefl _ hc
    · have hy := (α.property.rel_dom hc).1
      exact h (α.property.rel.antisymm (hr _ hy h) hc)

  simp [Form.vars] at hvars
  apply le_of_eq at hvars

  obtain ⟨v', hsat⟩ := (α.property.form_dom x).mpr hx
  sorry
