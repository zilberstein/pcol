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

def conj (α : Lpofin l) (S : Finset Node) : Form Node :=
  fun v ↦ ∀ x ∈ S, α.form x v

def branches_set (α : Lpofin l) : Set (Form Node) :=
  α.conj ''
  { S : Finset Node
  | S.Nonempty ∧
    S ⊆ α.extens ∧
    (α.conj S).sat ∧
    α.conj S ≤ α.stuck.not ∧
    ∀ T, S ⊂ T → T ⊆ α.extens → ¬ Form.sat (fun v ↦ ∀ x ∈ T, α.form x v)
  }

lemma branches_finite (α : Lpofin l) : α.branches_set.Finite := by
  refine Set.Finite.image _ ?_
  refine Set.Finite.subset α.extens.powerset.finite_toSet ?_
  intro s ⟨_, hsub, _⟩; simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, hsub]

noncomputable def branches (α : Lpofin l) : Finset (Form Node) := α.branches_finite.toFinset

lemma branches_set_monotone : @Monotone (Lpofin l) _ _ _ branches_set := by
  rintro α β hle φ ⟨S, ⟨hne, hsub, hsat, hstuck, hmax⟩, hφ⟩; subst hφ
  refine ⟨S, ⟨hne, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hsub (extens_monotone hle)
  · rcases hsat with ⟨v, hv⟩; use v; intro x hx
    refine (congrFun (hle.form x ?_) _).mp (hv x hx)
    have hx' := Finset.mem_of_mem_filter _ (hsub hx)
    simp only [nodes, Set.Finite.mem_toFinset] at hx'
    exact hx'
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
      Disjoint α.val.nodes (f φ).val.nodes ∧
      ∀ ψ, φ ≠ ψ → Disjoint (f φ).val.nodes (f ψ).val.nodes
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
      (φ ≤ α.form x ∧ y ∈ (f φ).val.nodes)
  lab x := if x ∈ α.nodes then α.lab x else ⨆ φ : ↑α.branches, (f φ).lab x
  form x := if x ∈ α.nodes then α.form x else fun v ↦ ∃ φ : ↑α.branches, (f φ).form x v
}

lemma branch_implies_node {α : Lpofin l} {x : Node} :
    ∀ φ ∈ α.branches, φ ≤ α.form x → x ∈ α.val.nodes := by
  intro φ hbr hle
  rcases (Set.Finite.mem_toFinset _).mp hbr with ⟨S, ⟨hne, hsub, hsat, hstk, hmax⟩, rfl⟩
  refine (α.val.property.form_dom x).mp ?_
  rcases hsat with ⟨v, hv⟩; use v; exact hle v hv

lemma seq_rel_valid [SupSet l] {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).rel.IsCausalityRel (seq_base α β f).nodes := by
  have h₁ := α.val.property
  have h₂ := β.val.property
  rcases f with ⟨f, hf⟩
  have hd₁ φ := (hf φ).2.1
  have hd₂ φ ψ := (hf φ).2.2 ψ
  have contra {P : Prop} {s t : Set Node} {x : Node} (hd : Disjoint s t)
      (hs : x ∈ s) (ht : x ∈ t) : P :=
    False.elim (Set.disjoint_left.mp hd hs ht)
  constructor
  -- Transitivity
  · rintro x y z (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyz | ⟨ψ, hyz | ⟨hy', hz⟩⟩)
    · left; exact h₁.rel.trans hxy hyz
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2
        ((f ψ).val.property.rel_dom hyz).1
    · right; use ψ; right; refine ⟨?_, hz⟩
      refine hy'.trans ?_; exact (h₁.form x (h₁.rel_dom hxy).1).2 y hxy
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 ((f φ).val.property.rel_dom hxy).2
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; left; exact (f φ).val.property.rel.trans hxy hyz
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyz).1
    · have hy := branch_implies_node ψ.val ψ.property hy'
      exact contra (hd₁ φ) hy ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 hy
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; right; refine ⟨hx, ?_⟩
        exact ((f φ).val.property.rel_dom hyz).2
      · exact contra (hd₂ φ ψ heq) hy ((f ψ).val.property.rel_dom hyz).1
    · have hy'' := branch_implies_node ψ.val ψ.property hy'
      exact contra (hd₁ φ) hy'' hy
  -- Antisymmetry
  · rintro x y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyx | ⟨ψ, hyx | ⟨hy', hx'⟩⟩)
    · exact h₁.rel.antisymm hxy hyx
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2 ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).1 hx'
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).2 ((f φ).val.property.rel_dom hxy).1
    · by_cases heq : φ = ψ
      · subst heq; exact (f φ).val.property.rel.antisymm hxy hyx
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ φ)
        (branch_implies_node ψ.val ψ.property hy')
        ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).1 hy
    · exact contra (hd₁ ψ) (branch_implies_node φ.val φ.property hx)
        ((f ψ).val.property.rel_dom hyx).2
    · exact contra (hd₁ ψ) (branch_implies_node φ.val φ.property hx) hx'
  -- Irreflexivity
  · rintro x (hxx | ⟨φ, hxx | ⟨hx, hx'⟩⟩)
    · exact h₁.rel.irrefl x hxx
    · exact (f φ).val.property.rel.irrefl x hxx
    · exact contra (hd₁ φ) (branch_implies_node φ.val φ.property hx) hx'
  -- Well-Foundedness
  · sorry
  -- Finite Levels
  · sorry
  -- Single-Rooted
  · obtain ⟨x, hroot⟩ := h₁.rel.single_rooted; use x; ext y; constructor
    · intro ⟨h, h'⟩; sorry
    · rintro rfl; sorry

noncomputable def seq [SupSet l] (α β : Lpofin l) (f : CopyFn α β) : Lpofin l := by
  refine Subtype.mk (Subtype.mk (seq_base α β f) ?_) ?_
  · constructor
    -- Rel Domain
    · intro x y hrel; cases hrel with
      | inl hrel =>
          refine ⟨Or.inl ?_, Or.inl ?_⟩
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).1
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).2
      | inr hrel =>
          rcases hrel with ⟨φ, (hrel | ⟨hx, hy⟩)⟩
          · constructor <;> refine Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)
            · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).1
            · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).2
          · refine ⟨Or.inl ?_, Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)⟩
            · simp only [nodes, Set.Finite.coe_toFinset]
              exact branch_implies_node φ.val φ.property hx
            · simp only [nodes, Set.Finite.coe_toFinset]; exact hy
    · intro x hx; apply (Set.mem_union _ _ _).mpr.mt at hx
      simp only [Finset.mem_coe, Set.mem_iUnion, Subtype.exists, not_or, not_exists] at hx
      rcases hx with ⟨hx, hx'⟩
      simp only [seq_base, Subtype.exists, hx, ↓reduceIte]
      sorry -- Need DCPO instance for l or something
    · exact seq_rel_valid
    · rintro x hlab y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩)
      · simp only [seq_base, nodes, Lpo.nodes, Set.Finite.coe_toFinset, Subtype.exists,
          Set.Finite.mem_toFinset, (α.val.property.rel_dom hxy).1, ↓reduceIte] at hlab
        exact α.val.property.bot _ hlab _ hxy
      · sorry
      · have hx' := branch_implies_node φ.val φ.property hx
        simp only [seq_base, nodes, Set.Finite.coe_toFinset, Subtype.exists,
          Set.Finite.mem_toFinset, hx', ↓reduceIte] at hlab
        rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨_, _, ⟨v, hv⟩, hstk, _⟩, heq⟩
        rw [← heq] at hx; have hform := hx v hv
        have hstk' := hstk v hv; simp only [Form.not, stuck, Subtype.exists, exists_and_left,
          exists_prop, not_exists, not_and] at hstk'
        refine hstk' x hlab ?_ hform; simp only [nodes, Set.Finite.mem_toFinset]; exact hx'
    · intro x; constructor
      · rintro ⟨v, hv⟩; by_cases hx : x ∈ α.nodes <;>
        simp only [seq_base, Subtype.exists, hx, ↓reduceIte] at hv
        · left; simp only [nodes, Set.Finite.coe_toFinset]
          exact (α.val.property.form_dom x).mp ⟨v, hv⟩
        · rcases hv with ⟨φ, hφ, h⟩; right
          simp only [Set.mem_iUnion, Finset.mem_coe, Subtype.exists]
          use φ; use hφ; simp only [nodes, Set.Finite.mem_toFinset]
          exact ((f ⟨φ, hφ⟩).val.property.form_dom x).mp ⟨v, h⟩
      · simp only [seq_base, nodes, Set.Finite.coe_toFinset, Subtype.exists,
          Set.Finite.mem_toFinset, Set.mem_union, Set.mem_iUnion]
        rintro (hx | ⟨φ, hφ, hx⟩)
        · simp only [Set.Finite.mem_toFinset, hx, ↓reduceIte]
          exact (α.val.property.form_dom x).mpr hx
        · have hx' : x ∉ α.val.nodes :=
            Set.disjoint_right.mp (f.2 ⟨φ, hφ⟩).2.1 hx
          simp only [Set.Finite.mem_toFinset, hx', ↓reduceIte]
          obtain ⟨v, hv⟩ := ((f ⟨φ, hφ⟩).val.property.form_dom x).mpr hx
          exact ⟨v, φ, hφ, hv⟩
    · sorry
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
