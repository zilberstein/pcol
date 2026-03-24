import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompletePartialOrder

def DSet (X : Type) [LE X] := { s : Set X // DirectedOn LE.le s ∧ s.Nonempty }

instance {X : Type} [LE X] : SetLike (DSet X) X where
  coe d := d.val
  coe_injective' := Subtype.val_injective

-- In Mathlib, CompletePartialOrder is pointed. Here is a version that does not
-- require the domain to be pointed, but requires directed sets to be nonempty
class DCPO (X : Type) extends PartialOrder X where
  dSup : DSet X → X
  lubOfDirected (d : DSet X) : IsLUB d.val (dSup d)

instance {X : Type} [CompletePartialOrder X] : DCPO X where
  dSup d := sSup d.val
  lubOfDirected d := CompletePartialOrder.lubOfDirected d.val d.property.1

namespace DSet

def directed {X : Type} [LE X] (d : DSet X) : DirectedOn LE.le d.val :=
    d.property.1

def nonempty {X : Type} [LE X] (d : DSet X) : d.val.Nonempty :=
    d.property.2

def dSup {X : Type} [DCPO X] : DSet X → X := DCPO.dSup

def le_dSup {X : Type} [DCPO X] {d : DSet X} {x : X} :
    x ∈ d → x ≤ d.dSup := by
  intro hx; exact (DCPO.lubOfDirected d).1 hx

def dSup_le {X : Type} [DCPO X] {d : DSet X} {x : X} :
    (∀ y ∈ d, y ≤ x) → d.dSup ≤ x := by
  intro hx; exact (DCPO.lubOfDirected d).2 hx

def image {X Y : Type} [Preorder X] [Preorder Y] (d : DSet X) (f : X → Y)
    (hf : Monotone f) : DSet Y := {
  val := f '' d.val
  property := by
    obtain ⟨hd, hne⟩ := d.property
    refine ⟨?_, hne.image _⟩
    intro _ hy₁ _ hy₂
    simp only [Set.mem_image, exists_exists_and_eq_and] at *
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, rfl⟩ := hy₂
    obtain ⟨x, hx, hle₁, hle₂⟩ := hd _ hx₁ _ hx₂
    exact ⟨x, hx, hf hle₁, hf hle₂⟩
}

lemma image_mem {X Y : Type} [Preorder X] [Preorder Y] {d : DSet X} {x : X}
    {f : X → Y} {hf : Monotone f} (h : x ∈ d) : f x ∈ d.image f hf := by
  exact Set.mem_image_of_mem _ h

lemma image_mono {X Y : Type} [Preorder X] [Preorder Y] {f : X → Y}
    {hf : Monotone f} : Monotone (fun d : DSet X ↦ d.image f hf) := by
  intro d d' hle y hy
  obtain ⟨x, hx, rfl⟩ := (Set.mem_image _ _ _).mp hy
  exact image_mem (hle hx)

-- Is this not in Mathlib?
lemma finite_upper_bound {X : Type} [Preorder X] {d : DSet X} {s : Set X}
    (hsub : s ⊆ d) (hfin : s.Finite) :
    ∃ α ∈ d, ∀ β ∈ s, β ≤ α := by
  refine hfin.induction_on_subset s ?_ ?_
  · obtain ⟨α, hα⟩ := d.nonempty
    refine ⟨α, hα, ?_⟩; intro β hc; exfalso; exact hc
  · intro α t hα hst hnt ⟨β, hβ, hub⟩
    obtain ⟨γ, hγ, hαγ, hβγ⟩ := d.directed _ (hsub hα) _ hβ
    refine ⟨γ, hγ, ?_⟩; intro γ' hγ'
    rcases Set.mem_insert_iff.mp hγ' with rfl | ht
    · exact hαγ
    · exact (hub _ ht).trans hβγ

def ScottContinuous {X Y : Type} [DCPO X] [DCPO Y] {f : X → Y} (hf : Monotone f): Prop :=
  ∀ d : DSet X, f d.dSup = (d.image f hf).dSup

end DSet

def way_below {X : Type} [DCPO X] (x y : X) : Prop :=
    ∀ d : DSet X,
      y ≤ d.dSup →
      ∃ z ∈ d, x ≤ z
infix:30 "≪" => way_below

def ScottCompact {X : Type} [DCPO X] (x : X) : Prop := x ≪ x

lemma bot_compact {X : Type} [DCPO X] [OrderBot X] :
    ScottCompact (⊥ : X) := by
  intro ⟨_, _, ⟨z, hz⟩⟩ _; exact ⟨z, hz, bot_le⟩
