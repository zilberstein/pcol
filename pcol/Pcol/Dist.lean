import Init.Prelude
import Mathlib

def Distr (α : Type) := { μ : WithBot α → ℝ // HasSum μ 1 ∧ ∀x, 0 ≤ μ x }

instance {α : Type} : FunLike (Distr α) (WithBot α) ℝ where
  coe d x := d.1 x
  coe_injective' _ _ h := Subtype.eq h

def supp {α : Type} (μ : Distr α) : Set (WithBot α) := { x | μ x ≠ 0 }

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
lemma hassum_le_bot {α : Type} {μ : Distr α} :
  ∑' (x : α), μ.1 x ≤ 1 := by {
    rcases μ with ⟨f, ⟨hs, hl⟩⟩
    have hs' := (Summable.hasSum_iff ⟨1, hs⟩).1 hs
    rw [← tsum_univ]
    have hhh := tsum_subtype_le f (Set.univ) hl ⟨1, hs⟩

    rw [hs'] at hhh
    simp
    rw [← hs']
    apply

  }

lemma sum_sup {α : Type} {f : α → ℝ } {r : ℝ} :
  (∑' x, f x) ≤ r ↔ iSup (fun s : Finset α => ∑ x ∈ s, f x) ≤ r:= by {
    sorry
   }

lemma sum_decomp {α : Type} :
  { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x } =
  Set.iInter (fun s : Finset α => { f : WithBot α → ℝ | (∑ x ∈ s, f x) ≤ 1 }) := by {

    calc
      { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x }
        = { f : WithBot α → ℝ | HasSum (fun ) 1 ∧ ∀ x, 0 ≤ f x }
    ext f; simp; constructor
    · intro hs s; sorry
    · sorry
  }

def fin_distrs {α : Type} := { μ : Distr α | Finite (supp μ ) }

-- Lemma B.4.2 of MM'05
lemma closed_finitary_half_space {α : Type} {f : WithBot α → NNReal} {r : NNReal} :
  Finite { x | f x ≠ 0 } →
  IsClosed { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * f x) ≤ r } := by {
    intro hf
    sorry
  }

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} (f : WithBot α → NNReal) (r : NNReal) :
  IsClosed { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * f x) ≤ r } := by {
    sorry
  }

lemma isClosed_distr {α : Type} :
  IsClosed { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x } := by {
    let const (_ : WithBot α) : NNReal := 1
    have h :
      { f : WithBot α → ℝ | HasSum f 1 ∧ ∀ x, 0 ≤ f x } =
      { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * const x) ≤ 1 } := by {
        ext f; simp; constructor
        · rintro ⟨hs, hl⟩; constructor
          · use ⟨f, ⟨hs, hl⟩⟩
          · unfold const; simp
            apply (Summable.hasSum_iff ⟨1, hs⟩).1 at hs
            rw [hs]
        · rintro ⟨⟨⟨g, ⟨hs, hl⟩⟩, heq⟩, hs'⟩
          simp [heq]; exact ⟨hs, hl⟩
    }
    rw [h]; exact (closed_infinitary_half_space const 1)
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

-- Intersection of sequence of closed sets of distributions is nonempty
theorem chain_inter_nonempty {α : Type} (c : ℕ → Set (Distr α)) :
  (∀ n : ℕ, c (n+1) ⊆ c n) →
  (∀ n : ℕ, IsClosed (c n) ∧ (c n).Nonempty) →
  (Set.iInter c).Nonempty := by {
    intro hc h
    apply (IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed c hc)
    · intro i; exact (h i).2
    · exact IsCompact.of_isClosed_subset CompactSpace.isCompact_univ (h 0).1 (Set.subset_univ (c 0))
    · intro i; exact (h i).1
  }
