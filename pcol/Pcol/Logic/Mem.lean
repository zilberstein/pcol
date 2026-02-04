import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Lattice.Union

import Pcol.Semantics.Basic

abbrev Var := Nat
abbrev Val := Nat
abbrev Mem := Finset Var × (Var → Option Val)

noncomputable instance : DecidableEq Mem := by
  classical
  infer_instance

class WellFormed (α : Type) where
  wf? : α → Prop

instance : GetElem Mem Var (Option Val) (fun _ _ => True) where
  getElem
  | (_, σ), x, _ => σ x

namespace Mem
  abbrev Inv := Invariant (fun _ => Finset Var) Mem

  instance : Membership Mem Inv where
    mem
    | (_, A), mem => mem ∈ A

  def empty : Mem := (∅, fun _ => .none)

  def dom : Mem → Finset Var := Prod.fst

  def wf? : Mem → Prop
  | (S, σ) => ∀ x, x ∈ S ↔ ∃ v, σ x = .some v

  -- Assumption: x not in domain
  def insert (x : Var) (v : Val) : Mem → Mem
  | (S, σ) =>
    (S ∪ {x} , fun y => if y = x then v else σ y)

  -- Assumption: projected set is subset of current domain
  def proj : Mem → Finset Var → Mem
  | (_, σ), S => (S, σ)

  noncomputable instance : CompatibleProj Mem Inv where
    -- Assumption: T ⊆ S
    cprojr
  | mem, (T, A) =>
    if mem.proj T ∈ A then mem else empty

  noncomputable instance : CompatibleProj Inv Inv where
    -- Assumption: both inv well-formed
    cprojr
    | (S, A), ℐ => (S , A.image (· ◃ ℐ))

  instance : Membership Var Mem where
    mem
    | (S, _),  x => (x ∈ S)

  -- Assumption: σ and τ are disjoint
  def union : Mem → Mem → Mem
  | (S, σ), (T, τ) =>
    (S ∪ T, fun y => if y ∈ S then σ y else τ y)

  infixr:65 " ⊎ " => union

  def disjoint : Mem → Mem → Prop
  | (S, _), (T, _) => Disjoint S T

end Mem

class Separation (α : Type) where
  sep : α → α → α

infixr:65 " ** " => Separation.sep

instance : Separation (Set Mem) where
  sep A B := { σ' | ∃ σ ∈ A, ∃ τ ∈ B, σ.disjoint τ ∧ σ' = σ ⊎ τ }

abbrev Mems := Finset Var × Set Mem

instance : Separation Mems where
  sep
  | (S, A), (T, B) =>
    (S ∪ T , A ** B)

namespace Mems
  def wf? : Mems -> Prop
  | (S, A) => ∀ mem ∈ A, mem.1 = S ∧ mem.wf?
end Mems

abbrev FinMems := Finset Var × Finset Mem

noncomputable instance : Separation FinMems where
  sep
  | (S, A), (T, B) =>
    (S ∪ T, A.biUnion (fun σ => B.biUnion (fun τ => { σ ⊎ τ })))

instance : Coe FinMems Mems where
  coe
  | (S, A) => (S, A)

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

lemma union_comm (σ₁ σ₂ : Mem) : σ₁ ⊎ σ₂ = σ₂ ⊎ σ₁ := sorry

lemma union_assoc (σ₁ σ₂ σ₃ : Mem) : σ₁ ⊎ (σ₂ ⊎ σ₃) = (σ₁ ⊎ σ₂) ⊎ σ₃ := sorry

--lemma union_comm_assoc (σ₁ σ₂ τ : Mem) : σ₁ ⊎ (σ₂ ⊎ τ) = σ₂ ⊎ (σ₁ ⊎ τ) := by
--    sorry
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
