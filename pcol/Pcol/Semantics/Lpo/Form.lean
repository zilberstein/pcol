import Init.Prelude
import Mathlib.Data.Set.Basic
import Mathlib.Data.Set.Disjoint
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.SymmDiff
import Mathlib.Order.SymmDiff

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

def DependsOn (p : Form α) (s : Set α) : Prop :=
  ∀ v v', Disjoint (symmDiff v v') s → p v = p v'

namespace DependsOn

lemma monotone (p : Form α) : Monotone p.DependsOn := by
  intro s t hsub hd v v' h
  refine hd v v' ?_
  exact Set.disjoint_of_subset_right hsub h

lemma true : (@Form.true α).DependsOn ∅ := by
  intro _ _ _; rfl

lemma false : (@Form.false α).DependsOn ∅ := by
  intro _ _ _; rfl

lemma literal {x : α} : (Form.literal x).DependsOn {x} := by
  intro v v' hd; ext; constructor; all_goals {
    intro h; have := Set.disjoint_right.mp hd (Set.mem_singleton _)
    have := Set.mem_symmDiff.mpr.mt this; simp only [not_or, not_and, not_not] at this
    try (exact this.1 h)
    try (exact this.2 h)
  }

lemma and {φ ψ : Form α} {s t : Set α} (h₁ : φ.DependsOn s) (h₂ : ψ.DependsOn t) :
    (φ.and ψ).DependsOn (s ∪ t) := by
  intro v v' hd; refine congrArg₂ And ?_ ?_
  · refine h₁.monotone _ ?_ v v' hd; exact Set.subset_union_left
  · refine h₂.monotone _ ?_ v v' hd; exact Set.subset_union_right

lemma or {φ ψ : Form α} {s t : Set α} (h₁ : φ.DependsOn s) (h₂ : ψ.DependsOn t) :
    (φ.or ψ).DependsOn (s ∪ t) := by
  intro v v' hd; refine congrArg₂ Or ?_ ?_
  · refine h₁.monotone _ ?_ v v' hd; exact Set.subset_union_left
  · refine h₂.monotone _ ?_ v v' hd; exact Set.subset_union_right

lemma not {φ : Form α} {s : Set α} (h : φ.DependsOn s) :
    φ.not.DependsOn s := by
  intro v v' hd; refine congrArg Not ?_; exact h v v' hd

lemma empty_vars {p : Form α} (hd : p.DependsOn ∅) (hsat : p.sat): p = Form.true := by
  ext v; conv => exact iff_true _
  have ⟨v', hform⟩ := hsat
  refine (hd v v' ?_).mpr hform
  exact Set.disjoint_empty _

end DependsOn

end Form
