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

lemma sat_on_vars {p : Form Node} {v₁ v₂ : Set Node} :
    (∀ x ∈ p.vars, x ∈ v₁ ↔ x ∈ v₂) → (p v₁ ↔ p v₂) := by
  let s := { x | ¬ (x ∈ v₁ ↔ x ∈ v₂) }
  sorry

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
  ⨆ n ∈ { n : ℕ | ∃ c : FinChain n a, ord.is_succ_chain c ∧ c.last = x }, ↑n

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

structure Lpo_base (l : Type) [Bot l] where
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

lemma lev_le_prec {l : Type} [Bot l] {a : Lpo l} {x : Node} (hx : x ∈ a.nodes) :
    a.rel.lev x ≤ { y | a.rel y x }.encard := sorry

lemma fin_lev {l : Type} [Bot l] {a : Lpo l} {x : Node} (hx : x ∈ a.nodes) :
    ∃ n : ℕ, a.rel.lev x = n := by
  have h : a.rel.lev x ≠ ⊤ := by
    refine ne_of_lt (lt_of_le_of_lt (lev_le_prec hx) ?_)
    refine lt_of_eq_of_lt (Set.Finite.encard_eq_coe_toFinset_card ?_) ?_
    · exact a.property.rel.fin_prec x
    · exact ENat.coe_lt_top _
  rcases ENat.ne_top_iff_exists.mp h with ⟨n, hn⟩
  exact ⟨n, hn.symm⟩

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
    have hzero := iSup_eq_bot.mp (iSup_eq_bot.mp hlev 1) ⟨c, hc, hl⟩
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

lemma lev_finite {l : Type} [Bot l] {α : Lpo l} {x : Node} (hx : x ∈ α.nodes) :
    ∃ n : ℕ, α.rel.lev x = n := by
  refine (fun hnt ↦ let ⟨n, h⟩ := ENat.ne_top_iff_exists.mp hnt; ⟨n, h.symm⟩) ?_
  obtain ⟨n, hfin⟩ := (α.property.rel.fin_prec x).exists_encard_eq_coe
  refine ne_top_of_le_ne_top (ENat.coe_ne_top n) ?_
  refine iSup₂_le ?_; rintro k ⟨c, hc, rfl⟩;
  have hcard : { x | ∃ k', k' < k ∧ x = c k'}.encard = ↑k := sorry
  rw [← hfin, ← hcard]
  refine Set.encard_mono ?_; rintro x ⟨k', hk, rfl⟩
  refine succ_chain_mono c hc (Fin.mk_lt_mk.mpr ?_)
  refine lt_of_eq_of_lt (Nat.mod_succ_eq_iff_lt.mpr ?_) hk
  linarith

lemma lev_mono {l : Type} [Bot l] {α : Lpo l} {x y : Node} (h : α.rel x y) :
    α.rel.lev x < α.rel.lev y := by
  obtain ⟨hx, hy⟩ := α.property.rel_dom h
  obtain ⟨n, hlev⟩ := lev_finite hx
  sorry
  -- simp only [Rel.lev, Set.mem_setOf_eq] at hlev
  -- have hne : Nonempty (∃ c : FinChain n Node, α.rel.is_succ_chain c ∧ c.last = x) := sorry
  -- obtain ⟨k, hk⟩ := ENat.exists_eq_iSup_of_lt_top (lt_of_eq_of_lt hlev (ENat.coe_lt_top _))
  -- have hne : Nonempty (k ∈ {n | ∃ c : FinChain n Node, α.rel.is_succ_chain c ∧ c.last = x}) := sorry
  -- rw [@iSup_const _ _ _ _ hne] at hk
  -- obtain ⟨k', hk'⟩ := ENat.exists_eq_iSup_of_lt_top (lt_of_eq_of_lt hk.symm (ENat.coe_lt_top _))
  -- have hhh : Nonempty (k' ∈ {n | ∃ c : FinChain n Node, α.rel.is_succ_chain c ∧ c.last = x}) := sorry
  -- rw [@iSup_const _ _ _ _ hhh] at hk'
  -- obtain ⟨k'', hk''⟩ := ENat.exists_eq_iSup_of_lt_top (lt_of_eq_of_lt hk'.symm (ENat.coe_lt_top _))

  -- revert x; induction n with
  -- | zero =>
  --   intro x hxy hx hlev; rw [hlev]
  --   refine bot_lt_iSup.mpr ⟨1, bot_lt_iSup.mpr ?_⟩
  --   simp only [bot_eq_zero', Nat.cast_one, zero_lt_one, Set.mem_setOf_eq, exists_prop, and_true]
  --   refine ⟨fun k ↦ if k.val = 0 then x else y, ?_, ?_⟩
  --   · intro k
