import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union

def Var := Nat
instance : DecidableEq Var := instDecidableEqNat

def Val := Nat
def Mem (v : Finset Var) := ↑v → Val

@[ext]
theorem mem_ext {u : Finset Var} {σ τ : Mem u} (h : ∀ x, σ x = τ x) : σ = τ := funext h

namespace Mem

noncomputable def union {u u₁ u₂ : Finset Var} (σ : Mem u₁) (τ : Mem u₂)
  (hu : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) : Mem u :=
  fun x ↦
    if h : x.val ∈ u₁ then
      σ ⟨x.val, h⟩
    else
      τ ⟨x.val, by
        obtain ⟨x, hx⟩ := x; rw [hu.2] at hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exfalso; exact h hx
        · exact hx
      ⟩
def emp : Mem ∅ := fun x ↦ False.elim (Finset.not_mem_empty _ x.property)

def castMem {u v : Finset Var} (σ : Mem u) (h : u = v) : Mem v :=
  cast (congrArg _ h) σ

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

end Mem

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

lemma union_comm_assoc {u u₁ u₂ v : Finset Var}
    {σ₁ : Mem (u₁ \ v)} {σ₂ : Mem (u₂ \ v)} {τ : Mem v}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)) =
    (σ₂.union (σ₁.union τ (dsj₁ hv)) (dsj₂₁ hu hv)) := by
  ext ⟨x, hx⟩; unfold Mem.union; by_cases hx' : x ∈ u₁ \ v
  · simp only [hx', ↓reduceDIte, Finset.mem_sdiff]; sorry
  · sorry

lemma sep_comm_assoc {u u₁ u₂ v : Finset Var}
    {A : Set (Mem (u₁ \ v))} {B : Set (Mem (u₂ \ v))} {I : Set (Mem v)}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    (Mem.sep A (Mem.sep B I (dsj₂ hv)) (dsj₁₂ hu hv)) =
    (Mem.sep B (Mem.sep A I (dsj₁ hv)) (dsj₂₁ hu hv)) := by sorry
