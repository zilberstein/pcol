import Init.Prelude
import Mathlib

def Distr (α : Type) := { μ : WithBot α → ℝ // HasSum μ 1 ∧ ∀x, 0 ≤ μ x }

instance {α : Type} : FunLike (Distr α) (WithBot α) ℝ where
  coe d x := d.1 x
  coe_injective' _ _ h := Subtype.eq h

lemma distr_upper_bound {α : Type} (μ : Distr α) (x : WithBot α) :
  μ x ≤ 1 := by {
    rcases μ with ⟨d, ⟨hs, hl⟩⟩
    exact (le_hasSum hs x (fun y _ => hl y))
  }

instance {α : Type} : TopologicalSpace (Distr α) :=
  TopologicalSpace.induced (fun μ => μ.1) Pi.topologicalSpace

lemma unit_interval_compact : IsCompact { r : ℝ | 0 ≤ r ∧ r ≤ 1 } := by {
  have h : { r : ℝ | 0 ≤ r ∧ r ≤ 1 } = Metric.closedBall 0.5 0.5 := by {
    ext r; constructor
    · intro hr; simp; rcases hr with ⟨hl, hu⟩
      rw [Real.dist_eq]
      apply abs_le'.2; constructor; linarith; linarith
    · intro hr; simp at hr
      rw [Real.dist_eq] at hr; apply abs_le'.1 at hr
      constructor; linarith; linarith
  }
  rw [h]
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · exact Metric.isClosed_closedBall
  · exists 1; simp; intros x hx y hy
    calc
      |x - y| = dist x y                := Real.dist_eq x y
      _       ≤ dist x 0.5 + dist 0.5 y := dist_triangle x 0.5 y
      _       = dist x 0.5 + dist y 0.5 := by rw [dist_comm 0.5 y]
      _       ≤ 1 := by linarith
}

lemma dist_decomp {α : Type} :
  Set.range (fun μ : Distr α => μ.1) =
  { f : WithBot α → ℝ | ∀ x, f x ∈  { r : ℝ | 0 ≤ r ∧ r ≤ 1 }} ∩
  { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x } := by {
    ext f; constructor
    · rintro ⟨⟨g, ⟨hs, hl⟩⟩, hf⟩; constructor
      · intro x
        rw [← hf]; simp
        exact ⟨hl x, distr_upper_bound ⟨g, ⟨hs, hl⟩⟩ x⟩
      · simp [← hf]; exact ⟨hs, hl⟩
    · simp; intro hlu hs hl
      use ⟨f, ⟨hs, hl⟩⟩
  }

lemma isClosed_distr {α : Type} :
  IsClosed { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x } := by {
    sorry
}

-- Lemma B.4.4 of MM'05
instance {α : Type} : CompactSpace (Distr α) := {
  isCompact_univ := by {
    have hi := (Topology.isInducing_iff (fun μ : Distr α => μ.1)).2 (by rfl)
    apply (Topology.IsInducing.isCompact_iff hi).2
    simp; rw [dist_decomp]
    apply IsCompact.inter_right
    · exact (isCompact_pi_infinite (fun _ => unit_interval_compact))
    · exact isClosed_distr
  }
}
