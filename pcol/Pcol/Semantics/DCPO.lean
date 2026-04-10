import Mathlib.Data.Set.Finite.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.OmegaCompletePartialOrder

def DSet (X : Type) [LE X] := { s : Set X // DirectedOn LE.le s ∧ s.Nonempty }

instance {X : Type} [LE X] : SetLike (DSet X) X where
  coe d := d.val
  coe_injective' := Subtype.val_injective

instance {X : Type} [LE X] : LE (DSet X) where
  le d d' := d.val ⊆ d'.val
instance {X : Type} [LE X] : PartialOrder (DSet X) where
  le_refl d := le_refl d.val
  le_trans d₁ d₂ d₃ := @le_trans _ _ d₁.val d₂.val d₃.val
  le_antisymm _ _ hle hge := Subtype.val_injective (le_antisymm hle hge)

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

def singleton {X : Type} [Preorder X] (x : X) : DSet X := {
  val := {x}
  property := by
    constructor
    · simp only [DirectedOn, Set.mem_singleton_iff, exists_eq_left, forall_eq, and_self]
      exact le_refl _
    · exact ⟨x, Set.mem_singleton _⟩
}

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

lemma mem_image {X Y : Type} [Preorder X] [Preorder Y] {d : DSet X} {y : Y}
    {f : X → Y} {hf : Monotone f} :
    y ∈ d.image f hf ↔ ∃ x ∈ d, f x = y := by
  constructor
  · intro h; exact (Set.mem_image f _ y).mp h
  · rintro ⟨x, hx, rfl⟩; exact image_mem hx

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

def insert {X : Type} [Preorder X] {x : X} {d d' : DSet X}
    (hfin : d.val.Finite) (hsub : d.val ⊆ d'.val) (hmem : x ∈ d') : DSet X :=
have hu := finite_upper_bound (Set.insert_subset hmem hsub) (hfin.insert x)
{
  val := (d.val.insert x).insert hu.choose
  property := by
    constructor
    · intro y hy z hz
      refine ⟨hu.choose, Set.mem_insert _ _, ?_, ?_⟩ <;>
      rcases Set.eq_or_mem_of_mem_insert hy with rfl | hy <;>
        rcases Set.eq_or_mem_of_mem_insert hz with rfl | hz
      all_goals {
        try (exact le_refl _)
        try (refine hu.choose_spec.2 _ ?_; assumption)
      }
    · exact ⟨hu.choose, Set.mem_insert _ _⟩
}

def ScottContinuous {X Y : Type} [DCPO X] [DCPO Y] {f : X → Y} (hf : Monotone f): Prop :=
  ∀ d : DSet X, f d.dSup = (d.image f hf).dSup

end DSet

def way_below {X : Type} [DCPO X] (x y : X) : Prop :=
    ∀ d : DSet X,
      y ≤ d.dSup →
      ∃ z ∈ d, x ≤ z
infix:30 "≪" => way_below

def IsScottCompact {X : Type} [DCPO X] (x : X) : Prop := x ≪ x

lemma bot_compact {X : Type} [DCPO X] [OrderBot X] :
    IsScottCompact (⊥ : X) := by
  intro ⟨_, _, ⟨z, hz⟩⟩ _; exact ⟨z, hz, bot_le⟩

class ScottCompact (X : Type) [DCPO X] where
  scottCompact (x : X) : IsScottCompact x

open OmegaCompletePartialOrder

namespace Chain

def to_dSet {X : Type} [DCPO X] (c : Chain X) : DSet X :=
  ⟨ Set.range c, by {
    constructor
    · intro x hx y hy
      obtain ⟨n, rfl⟩ := Set.mem_range.mp hx
      obtain ⟨m, rfl⟩ := Set.mem_range.mp hy
      refine ⟨c (max n m), Set.mem_range.mpr ⟨max n m, rfl⟩, ?_, ?_⟩
      · exact c.monotone' le_sup_left
      · exact c.monotone' le_sup_right
    · exact ⟨(c 0), Set.mem_range.mpr ⟨0, rfl⟩⟩
  } ⟩

def lfp {X : Type} [OmegaCompletePartialOrder X] [OrderBot X]
    (f : X → X) (hf : Monotone f) : X :=
  ωSup (fixedPoints.iterateChain ⟨f, hf⟩ ⊥ bot_le)

theorem lfp_is_lfp {X : Type} [OmegaCompletePartialOrder X] [OrderBot X]
    {f : X → X} (hc : ωScottContinuous f):
    IsLeast f.fixedPoints (lfp f hc.monotone) := by
  let f' := ContinuousHom.mk ⟨f, _⟩ hc.map_ωSup
  constructor
  · exact fixedPoints.ωSup_iterate_mem_fixedPoint f' _ _
  · intro x hx; exact fixedPoints.ωSup_iterate_le_fixedPoint f' _ _ hx bot_le

end Chain

instance {X : Type} [DCPO X] : OmegaCompletePartialOrder X where
  ωSup c := (Chain.to_dSet c).dSup
  le_ωSup c i := DSet.le_dSup (Set.mem_range.mpr ⟨i, rfl⟩)
  ωSup_le c x h := by
    refine DSet.dSup_le ?_; intro d hd
    obtain ⟨i, rfl⟩ := Set.mem_range.mp hd
    exact h i

instance {X Y : Type} [OmegaCompletePartialOrder Y] : OmegaCompletePartialOrder (X → Y) where
  ωSup c := fun x ↦ ωSup {
    toFun n := c n x
    monotone' i j hle := c.monotone' hle x
  }
  le_ωSup := by
    intro c i x; simp only; refine le_of_eq_of_le ?_ (le_ωSup _ i); rfl
  ωSup_le := by
    intro c f hle x; simp only; refine ωSup_le _ _ ?_
    intro i; exact hle i x

instance {X Y : Type} [LE Y] [OrderBot Y] : OrderBot (X → Y) where
  bot_le _ _ := bot_le
