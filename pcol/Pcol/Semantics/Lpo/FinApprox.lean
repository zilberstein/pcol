import Mathlib
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.Isomorphism

def Lpofin (l : Type) [Bot l] := { a : Lpo l // a.nodes.Finite }

instance {l : Type} [LE l] [Bot l] : LE (Lpofin l) where
  le a b := LE.le a.val b.val
instance {l : Type} [Preorder l] [Bot l] : Preorder (Lpofin l) :=
  Preorder.lift Subtype.val
instance {l : Type} [PartialOrder l] [Bot l] : PartialOrder (Lpofin l) :=
  PartialOrder.lift Subtype.val Subtype.val_injective
instance {l : Type} [Bot l] : Coe (Lpofin l) (Lpo l) where
  coe := Subtype.val

namespace Lpofin

noncomputable def nodes {l : Type} [Bot l] (a : Lpofin l) := a.property.toFinset
def rel {l : Type} [Bot l] (a : Lpofin l) := a.val.rel
def lab {l : Type} [Bot l] (a : Lpofin l) := a.val.lab
def form {l : Type} [Bot l] (a : Lpofin l) := a.val.form

 def IsIsomorphic {l : Type} [Bot l] (a b : Lpofin l) : Prop :=
  a.val.IsIsomorphic b.val

lemma isoEquivalence {l : Type} [Bot l] : Equivalence (@IsIsomorphic l _) := by {
  constructor <;> simp [IsIsomorphic]
  -- Reflexivity
  · intro a; exact Lpo.isoEquivalence.refl a.val
  -- Symmetry
  · intro _ _ h; exact Lpo.isoEquivalence.symm h
  -- Transitivity
  · intro _ _ _ hab hbc; exact Lpo.isoEquivalence.trans hab hbc
}

instance instSetoid {l : Type} [Bot l] : Setoid (Lpofin l) where
  r := IsIsomorphic
  iseqv := isoEquivalence

end Lpofin

namespace Lpo

noncomputable def trunc {l : Type} [Bot l] (a : Lpo l) (n : ℕ) : Lpofin l :=
  let p x := a.rel.lev x ≤ n
  let a : Lpo l := Subtype.mk {
    nodes := { x ∈ a.nodes | p x }
    rel x y := a.rel x y ∧ p x ∧ p y
    lab x := if a.rel.lev x < n then a.lab x else ⊥
    form x := if p x then a.form x else Form.false
  } (by {
    unfold p; constructor <;> simp
    · intro x y hr hx hy
      rcases a.property.rel_dom hr with ⟨hxa, hya⟩
      exact ⟨⟨hxa, hx⟩, hya, hy⟩
    · intro x hx hlev; by_cases h : x ∈ a.nodes
      · apply hx at h; linarith
      · exact a.property.lab_dom x h
    · constructor
      · intro x y z ⟨hxy, hx, _⟩ ⟨hyz, _, hz⟩
        exact ⟨a.property.rel.trans hxy hyz, hx, hz⟩
      · intro x y ⟨hxy, _⟩ ⟨hyx, _⟩
        exact a.property.rel.antisymm hxy hyx
      · intro x ⟨hc, _⟩; exact a.property.rel.irrefl x hc
      · sorry
      · sorry
      · sorry
    · intro x hx y hxy hlev
      -- If lev x = n, then the claim is trivial
      -- If not, then lev x < n, and so lab x = ⊥, therefore x cannot have
      -- successions, and so hxy is a contradiction
      sorry
    · sorry
    · sorry
  })
  Subtype.mk a (by {
    sorry
  })

lemma trunc_equiv {l : Type} [Bot l] {a b : Lpo l} {n : ℕ}
  (heq : a ≈ b) : trunc a n ≈ trunc b n := by {
  rcases heq with ⟨e, h⟩
  sorry
  --refine ⟨e, ?_⟩
}

lemma trunc_le {l : Type} [Preorder l] [OrderBot l] {a : Lpo l} {n : ℕ} :
  a.trunc n ≤ a := by {
  constructor <;> simp [Lpo.trunc, Lpo.nodes, Lpo.rel, Lpo.lab, Lpo.form]
  · intro x hx y hyx; simp at *
    --Need a lemma that if lev x ≤ n and y < x, then lev y ≤ n
    exact ⟨(a.property.rel_dom hyx).1, sorry⟩
  · intro _ _ hxl _ _ hyl _; exact ⟨hxl, hyl⟩
  · intro x; by_cases hx : a.rel.lev x < n <;>
      unfold Lpo.rel at hx <;> simp [hx, bot_le]
  · intro _ _ _ _; linarith
  · sorry
}

lemma trunc_mono {l : Type} [Bot l] [LE l] {a b : Lpo l} {n m : ℕ}
  (hab : a ≤ b) (hnm : n ≤ m) : a.trunc n ≤ b.trunc m := by sorry

end Lpo
