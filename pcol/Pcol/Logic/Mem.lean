import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union

abbrev Var := Nat
abbrev Val := Nat
abbrev Mem := List (Var × Val)

namespace Mem

def insert (x: Var) (v: Val) (σ: Mem) : Mem :=
  match σ with
  | [] => [(x, v)]
  | (y, v') :: σ' =>
    if x ≤ y then
      (x, v) :: (y, v') :: σ'
    else
      (y, v') :: insert x v σ'

def lookup (x: Var) (σ: Mem) : Option Val :=
  match σ with
  | [] => none
  | (y, v) :: σ' =>
    if x = y then some v else lookup x σ'

def union (σ τ: Mem) : Mem :=
  match σ with
  | [] => τ
  | (x, v) :: σ' => insert x v (union σ' τ)

infixr:65 " ⊎ " => union

def list_greater (x: Var) (σ: Mem) : Prop :=
  match σ with
  | [] => True
  | (y, _) :: σ' => x < y ∧ list_greater x σ'

def wf? (σ: Mem) : Prop :=
  match σ with
  | [] => True
  | (x, _) :: σ' => list_greater x σ' ∧ wf? σ'

instance : GetElem Mem Var (Option Val) (fun _ _ => True) where
  getElem σ x _ := lookup x σ

def indom (x: Var) (σ: Mem) : Prop :=
    match σ with
    | [] => False
    | (y, _) :: σ' => if x = y then True else indom x σ'

instance : Membership Var Mem where
  mem σ x := indom x σ

def disjoint (σ τ: Mem) : Prop :=
  match σ with
  | [] => True
  | (x, _) :: σ' => lookup x τ = none ∧ disjoint σ' τ

instance {σ τ} : Decidable (disjoint σ τ) := by
  induction σ generalizing τ with
  | nil =>
    simp [disjoint]
    exact instDecidableTrue
  | cons p σ' ih =>
    simp [disjoint]
    exact instDecidableAnd

end Mem

def wfₛ (A : Set Mem) : Set Mem := { σ ∈ A | σ.wf? }

class Separation (α : Type) where
  sep : α → α → α

infixr:65 " ** " => Separation.sep

instance : Separation (Set Mem) where
  sep A B :=
    { σ' | ∃ σ ∈ A, ∃ τ ∈ B, σ.disjoint τ ∧ σ' = σ ⊎ τ }

instance : Separation (Finset Mem) where
  sep A B :=
    A.biUnion (fun σ =>
      B.biUnion (fun τ =>
        if σ.disjoint τ then { σ ⊎ τ } else {}
      )
    )
   --   Finset.image (σ ∪ ·) (B.filter (σ.disjoint))

/-

noncomputable def sep {u u₁ u₂ : Finset Var} (A : Set (Mem u₁)) (B : Set (Mem u₂))
    (hu : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) :
    Set (Mem u) :=
  ⋃ σ ∈ A, ⋃ τ ∈ B, { σ.union τ hu }

lemma sep_emp {u : Finset Var} (σ : Mem u) :
    σ.union emp ⟨Finset.disjoint_empty_right _, (Finset.union_empty _).symm⟩ = σ := by sorry

def proj {u v : Finset Var} (σ : Mem u) (h : v ⊆ u) : Mem v :=
  fun x ↦ σ ⟨x.val, h x.property⟩

lemma union_mem {u u₁ u₂ : Finset Var} {σ : Mem u₁} {τ : Mem u₂} {A : Set (Mem u₁)} {B : Set (Mem u₂)}
    (h : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) :
    σ.union τ h ∈ Mem.sep A B h ↔ σ ∈ A ∧ τ ∈ B := by
  sorry
-/


/-
-- Shorthands for some disjointness lemmas
lemma dsj₁ {u₁ u₂ v : Finset Var} (h : v = u₁ ∩ u₂) :
    Disjoint (u₁ \ v) v ∧ u₁ = (u₁ \ v) ∪ v := by
  refine ⟨Finset.sdiff_disjoint, (Finset.sdiff_union_of_subset ?_).symm⟩
  rw [h]; exact Finset.inter_subset_left

lemma dsj₂ {u₁ u₂ v : Finset Var} (h : v = u₁ ∩ u₂) :
    Disjoint (u₂ \ v) v ∧ u₂ = (u₂ \ v) ∪ v :=
  dsj₁ (h.trans (Finset.inter_comm _ _))

lemma dsj₁₂ {u₁ u₂ u v : Finset Var} (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    Disjoint (u₁ \ v) u₂ ∧ u = (u₁ \ v) ∪ u₂ := by
  rw [hv, Finset.sdiff_inter_self_left]; constructor
  · exact Finset.sdiff_disjoint
  · exact hu.trans Finset.sdiff_union_self_eq_union.symm

lemma dsj₂₁ {u₁ u₂ u v : Finset Var} (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    Disjoint (u₂ \ v) u₁ ∧ u = (u₂ \ v) ∪ u₁ :=
  dsj₁₂ (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _))
-/

lemma union_comm_assoc (σ₁ σ₂ τ : Mem) : σ₁ ⊎ (σ₂ ⊎ τ) = σ₂ ⊎ (σ₁ ⊎ τ) := by
    sorry
--  ext ⟨x, hx⟩; unfold Mem.union; by_cases hx' : x ∈ u₁ \ v
--  · simp only [hx', ↓reduceDIte, Finset.mem_sdiff]; sorry
--  · sorry

lemma sep_comm_assoc (A B C : Set Mem) : A ** (B ** C) = B ** (A ** C) := by
  sorry

/-
lemma sep_comm_assoc {u u₁ u₂ v : Finset Var}
    {A : Set (Mem (u₁ \ v))} {B : Set (Mem (u₂ \ v))} {I : Set (Mem v)}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    (Mem.sep A (Mem.sep B I (dsj₂ hv)) (dsj₁₂ hu hv)) =
    (Mem.sep B (Mem.sep A I (dsj₁ hv)) (dsj₂₁ hu hv)) := by sorry
-/
