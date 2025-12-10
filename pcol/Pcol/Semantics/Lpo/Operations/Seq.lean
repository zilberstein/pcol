import Mathlib

import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Order

namespace Lpofin

variable {l : Type} [PartialOrder l] [OrderBot l]

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin l) : Form Node :=
  fun v ↦ ∃ x : α.nodes, α.lab x = ⊥ ∧ α.form x v

lemma stuck_antitone : @Antitone (Lpofin l) _ _ _ stuck := by
  intro α β hle v ⟨⟨x, hmem⟩, hlab, hform⟩
  by_cases hx : x ∈ α.nodes
  · refine ⟨⟨x, hx⟩, ?_, ?_⟩
    · refine le_antisymm ?_ bot_le
      rw [← hlab]; exact hle.lab x
    · have hf := hle.form x
      simp [Lpofin.nodes] at hx
      simp [Lpofin.form]
      rw [congrFun (hf hx) v]; exact hform
  · sorry -- need to show that there exists some bot node lower down in the order

-- A node is in the exntensible set if it is possible for it not be stuck
noncomputable def extens (α : Lpofin l) : Finset Node :=
  α.nodes.filter fun x ↦ ¬ α.form x ≤ α.stuck

lemma extens_not_bot {α : Lpofin l} {x : Node} : x ∈ α.extens → α.lab x ≠ ⊥ := by
  intro h; simp [extens] at h; intro heq; apply h.2; intro v hform
  have hx := (α.val.property.form_dom x).mp ⟨v, hform⟩
  refine ⟨⟨x, ?_⟩, heq, hform⟩
  · simp [Lpofin.nodes]; exact hx

lemma extens_subset_nodes {α : Lpofin l} : α.extens ⊆ α.nodes := by
  intro x hx; simp [extens] at hx; exact hx.1
  -- refine (α.val.property.form_dom x).mp ?_
  -- simp [LE.le] at hx; rcases hx with ⟨v, hf, _⟩
  -- exact ⟨v, hf⟩

lemma extens_monotone : @Monotone (Lpofin l) _ _ _ extens := by
  intro α β hle x; simp [extens]; intro hx hstuck
  simp [Lpofin.nodes] at *;
  refine ⟨hle.nodes hx, fun hc ↦ ?_⟩
  refine hstuck (fun v hform ↦ stuck_antitone hle v (hc v ?_))
  simp [Lpofin.form]; rw [← hle.form x hx]; exact hform

def branches_set (α : Lpofin l) : Set (Form Node) :=
  (fun S v ↦ ∀ x ∈ S, α.form x v) ''
  { S : Finset Node
  | S.Nonempty ∧
    S ⊆ α.extens ∧
    (∀ v, (∀ x ∈ S, α.form x v) → ¬ α.stuck v) ∧
    ∀ T, S ⊂ T → T ⊆ α.extens → ¬ Form.sat (fun v ↦ ∀ x ∈ T, α.form x v)
  }

lemma branches_finite (α : Lpofin l) : α.branches_set.Finite := by
  refine Set.Finite.image _ ?_
  refine Set.Finite.subset α.extens.powerset.finite_toSet ?_
  intro s ⟨_, hsub, _⟩; simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, hsub]

noncomputable def branches (α : Lpofin l) : Finset (Form Node) := α.branches_finite.toFinset

lemma branches_set_monotone : @Monotone (Lpofin l) _ _ _ branches_set := by
  rintro α β hle φ ⟨S, ⟨hne, hsub, hstuck, hmax⟩, hφ⟩; subst hφ
  refine ⟨S, ⟨hne, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hsub (extens_monotone hle)
  · intro v hform hstuck'; refine hstuck v ?_ ?_
    · intro x hx; refine (congr_fun (hle.form x ?_) v).mpr (hform x hx)
      have hx' := Finset.mem_of_mem_filter _ (hsub hx)
      simp only [nodes, Set.Finite.mem_toFinset] at hx'
      exact hx'
    · exact stuck_antitone hle v hstuck'
  · intro T hST hT hc; refine hmax T hST ?_ ?_; sorry; sorry
  · ext1 v; refine forall_congr fun x ↦ ?_; ext; constructor
    · intro h hx; refine (congr_fun (hle.form x ?_) v).mpr (h hx)
      have hx' := Finset.mem_of_mem_filter _ (hsub hx)
      simp only [nodes, Set.Finite.mem_toFinset] at hx'
      exact hx'
    · intro h hx; refine (congr_fun (hle.form x ?_) v).mp (h hx)
      have hx' := Finset.mem_of_mem_filter _ (hsub hx)
      simp only [nodes, Set.Finite.mem_toFinset] at hx'
      exact hx'

lemma branches_monotone : @Monotone (Lpofin l) _ _ _ branches := by
  unfold branches; intro α β hle; simp; exact branches_set_monotone hle

def CopyFn (α β : Lpofin l) : Type :=
  { f : ↑α.branches → Lpofin l //
    ∀ φ : ↑α.branches,
      f φ ≈ β ∧
      (f φ).nodes ∩ α.nodes = ∅ ∧
      ∀ ψ, φ ≠ ψ → (f φ).nodes ∩ (f ψ).nodes = ∅
  }
instance {α β : Lpofin l} : FunLike (CopyFn α β) ↑α.branches (Lpofin l) where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.eq h

def CopyFn_extends {α α' β β' : Lpofin l}
    (hle : α ≤ α') (f : CopyFn α β) (g : CopyFn α' β') :=
  ∀ φ : ↑α.branches, f φ ≤ g ⟨φ.val, branches_monotone hle φ.property⟩

noncomputable def seq_base [SupSet l] (α β : Lpofin l) (f : CopyFn α β) : Lpo_base l := {
  nodes := α.nodes ∪ ⋃ φ : ↑α.branches, (f φ).nodes
  rel x y :=
    α.rel x y ∨
    ∃ φ : ↑α.branches,
      (f φ).rel x y ∨
      (φ ≤ α.form x ∧ y ∈ (f φ).nodes)
  lab x := if x ∈ α.nodes then α.lab x else ⨆ φ : ↑α.branches, (f φ).lab x
  form x := if x ∈ α.nodes then α.form x else fun v ↦ ∃ φ : ↑α.branches, (f φ).form x v
}

noncomputable def seq [SupSet l] (α β : Lpofin l) (f : CopyFn α β) : Lpofin l := by
  refine Subtype.mk (Subtype.mk (seq_base α β f) ?_) ?_
  · simp [seq_base]; constructor
    · simp; intro x y hrel; cases hrel with
      | inl hrel =>
          refine ⟨Or.inl ?_, Or.inl ?_⟩
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).1
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).2
      | inr hrel =>
          rcases hrel with ⟨φ, hφ, (⟨hrel⟩ | ⟨hx, hy⟩)⟩
          · refine ⟨Or.inr ⟨φ, hφ, ?_⟩, Or.inr ⟨φ, hφ, ?_⟩⟩
            · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).1
            · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).2
          · refine ⟨Or.inl ?_, Or.inr ⟨φ, hφ, hy⟩⟩
            · sorry
    · simp; intro x hx hbr; simp [hx]; sorry
    · simp; sorry
    · simp; intro x hx y; refine ⟨?_, fun φ hφ ↦ ⟨?_, ?_⟩⟩
      · refine α.val.property.bot x ?_ y; by_cases hx' : x ∈ α.nodes
        · simp [hx'] at hx; exact hx
        · simp [Lpofin.nodes] at hx'; exact α.val.property.lab_dom x hx'
      · sorry
      · sorry
    · simp; intro x; sorry
    · simp; intro x hx; sorry
  · simp [Lpo.nodes, seq_base]; refine Set.finite_iUnion ?_
    intro ⟨φ, hφ⟩; simp

lemma seq_monotone [SupSet l] {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hle₁ : α ≤ α') (hle₂ : β ≤ β') (hext : CopyFn_extends hle₁ f g) :
    seq α β f ≤ seq α' β' g := by
  constructor
  · simp only [Lpo.nodes, seq, seq_base, nodes, Set.Finite.coe_toFinset, Set.Finite.mem_toFinset,
      Subtype.exists, Set.union_subset_iff, Set.iUnion_subset_iff, Subtype.forall]
    constructor
    · intro x hx; left; exact hle₁.nodes hx
    · intro φ hφ x hx; right
      have hφ' := branches_monotone hle₁ hφ
      simp only [Set.mem_iUnion, Subtype.exists]
      exact ⟨φ, hφ', (hext ⟨φ, hφ⟩).nodes hx⟩
  · simp only [Rel.is_down_closed, Lpo.nodes, seq, seq_base, Subtype.exists, Set.mem_union,
      Finset.mem_coe, Set.mem_iUnion, Lpo.rel]
    intro x hx y hy; sorry
  · simp only [Lpo.nodes, seq, seq_base, Subtype.exists, Set.mem_union, Finset.mem_coe,
      Set.mem_iUnion, Lpo.rel, eq_iff_iff]
    intro x hx y hy; sorry
  · intro x; by_cases hx : x ∈ α.nodes
    · have hx' : x ∈ α'.nodes := by
        simp only [nodes, Set.Finite.mem_toFinset] at *
        exact hle₁.nodes hx
      simp only [Lpo.lab, seq, seq_base, Subtype.exists, hx, ↓reduceIte, hx', ge_iff_le]
      exact hle₁.lab x
    · sorry -- simp [seq, seq_base, hx, Lpo.lab]
  · sorry
  · sorry

end Lpofin
