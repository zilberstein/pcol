import Mathlib

def Node := ℕ
instance : Inhabited Node where
  default := (0 : ℕ)

instance {x y : Node} : Decidable (x = y) := sorry


def Form (α : Type) := Set α → Prop

@[ext]
lemma form_ext {α : Type} {φ ψ : Form α} (h : ∀ x, φ x = ψ x) : φ = ψ := by sorry

namespace Form

def true {α : Type} : Form α := fun _ => True
def false {α : Type} : Form α := fun _ => False
def and {α : Type} (p : Form α) (q : Form α) : Form α := fun v => p v ∧ q v
def not {α : Type} (p : Form α) : Form α := fun v => ¬(p v)
def literal {α : Type} (x : α) : Form α := fun v => x ∈ v

def sat {α : Type} (p : Form α) : Prop := ∃ v, p v

-- Need to work this part out
instance {α : Type} : DecidablePred (Form.true : Set α → Prop) := by sorry
instance {α : Type} : DecidablePred (Form.false : Set α → Prop) := by sorry
instance {α : Type} {φ ψ : Form α} [DecidablePred φ] [DecidablePred ψ] :
  DecidablePred (Form.and φ ψ : Set α → Prop) := by sorry
instance {α : Type} {φ : Form α} [DecidablePred φ] :
  DecidablePred (Form.not φ : Set α → Prop) := by sorry
instance {α : Type} : DecidablePred (Form.sat : Form α → Prop) := by sorry

instance {α : Type} : LE (Form α) where
  le φ ψ := ∀ v, φ v → ψ v
instance {α : Type} {φ ψ : Form α} : Decidable (φ ≤ ψ) := by sorry

instance {α : Type} : Preorder (Form α) where
  le_refl φ v h := h
  le_trans φ ψ ξ h₁ h₂ v hφ := h₂ v (h₁ v hφ)

instance {α : Type} : PartialOrder (Form α) where
  le_antisymm φ ψ h₁ h₂ := by ext v; exact ⟨h₁ v, h₂ v⟩

def vars (p : Form Node) : Set Node :=
  { x | ∃ v, p v ≠ p (fun y => if x = y then ¬(v y) else v y) }

end Form

namespace Rel

def succ {a : Type} (ord : Rel a a) (x : a) : Set a :=
  fun y => ord x y ∧ ∀ z, ¬(ord x z ∧ ord z y)

def roots {a : Type} (ord : Rel a a) : Set a := { x : a | ∀ y, ¬(ord y x) }

def is_succ_chain {α : Type} (ord : Rel α α) (l : List α) : Prop :=
  match l with
  | [] => False
  | List.cons x xs =>
    (xs.foldr (fun (x : α) (acc : α × Prop) => (x, acc.2 ∧ x ∈ ord.succ acc.1)) (x, True)).2

def is_down_closed (ord : Rel Node Node) (X : Set Node) : Prop :=
  ∀ x ∈ X, ∀ y, ord y x → y ∈ X

def IsUpClosed (ord : Rel Node Node) (X : Set Node) : Prop :=
  ∀ x ∈ X, ∀ y, ord x y → y ∈ X

def up_closure (ord : Rel Node Node) (X : Set Node) : Set Node :=
  { x | ∃ y ∈ X, ord y x }

noncomputable def lev {a : Type} (ord : Rel a a) (x : a) : ℕ :=
  sSup { n : ℕ | ∃ l : List a, n = l.length - 1 ∧ is_succ_chain ord l ∧ l.getLast? = Option.some x }

structure IsCausalityRel {α : Type} (ord : Rel α α) (s : Set α) : Prop where
  -- ord is a strict partial order
  trans : Transitive ord
  antisymm : AntiSymmetric ord
  irrefl : Irreflexive ord
  -- ord is finitely preceeded
  wf : WellFounded ord
  -- each level is finite
  fin_lev: ∀ n : ℕ, (ord.lev ⁻¹' {n}).Finite
  -- ord is single-rooted
  single_rooted : ∃ x, ord.roots ∩ s = {x}

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
          ∀ z, a.rel x z → ∀ v, a.form z v → a.form x v


def Lpo (l : Type) [Bot l] := { α : Lpo_base l // is_valid_lpo α }

namespace Lpo

def nodes {l : Type} [Bot l] (a : Lpo l) : Set Node := a.val.nodes
def rel {l : Type} [Bot l] (a : Lpo l) : Rel Node Node := a.val.rel
def lab {l : Type} [Bot l] (a : Lpo l) : Node → l := a.val.lab
def form {l : Type} [Bot l] (a : Lpo l) : Node → Form Node := a.val.form

def bots {l : Type} [Bot l] (a : Lpo l) : Set ↑a.nodes := { x | a.lab x = ⊥}

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
      · constructor; intro x; constructor; intro _ hc; contradiction
      · intro n; simp [Rel.lev, Set.preimage] ; sorry
        --refine Set.finite_singleton ?_
      · use x; simp [Rel.roots]
    · intro y; constructor
      · rintro ⟨v, h⟩; by_cases heq : x = y
        · exact Eq.symm heq
        · rw [ite_cond_eq_false _ _ (eq_false heq)] at h
          simp [Form.false] at h
      · intro heq; use ∅
        rw [ite_cond_eq_true _ _ (eq_true (Eq.symm heq))]; simp [Form.true]
    · intro y; simp [Form.true, Form.vars]
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
  · intro ⟨heq, hrel, hlab, hform⟩
    cases a; cases b; sorry
}
