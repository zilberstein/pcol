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

def fin_exp (α : Type) := { f : WithBot α → NNReal // Finite { x | f x ≠ 0 } }

def restr {α : Type} [DecidableEq α] (f : WithBot α → NNReal) (s : Finset (WithBot α)) : fin_exp α :=
  Subtype.mk (fun x => if x ∈ s then f x else 0)
  (by {
    apply Set.Finite.subset (Finset.finite_toSet s)
    intros x hx; simp at hx; exact hx.1
  })

-- Lemma B.4.2 of MM'05
lemma closed_finitary_half_space {α : Type} {f : fin_exp α} {r : NNReal} :
  IsClosed { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * f.val x) ≤ r } := by {
    sorry
  }

-- I think this is true, but worst case we can make f bounded
lemma convex_sum_summable {α : Type} {f : WithBot α → NNReal} {μ : Distr α} :
  Summable (fun x => μ.val x * f x) := by {
    sorry
  }

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} [DecidableEq α] (f : WithBot α → NNReal) (r : NNReal) :
  IsClosed { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * f x) ≤ r } := by {
    have he :
      { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * f x) ≤ r } =
      Set.iInter (fun s : Finset (WithBot α) =>
        { g | (∃ μ : Distr α, g = μ.val) ∧ (∑' x, g x * (restr f s).val x) ≤ r }) := by {
          ext g; simp; constructor
          · rintro ⟨⟨μ, heq⟩, hle⟩ s; constructor
            · use μ
            · have hr : ∀ x, (restr f s).val x ≤ f x := by {
                intro x; unfold restr; simp
                by_cases h: x ∈ s
                · simp [h]
                · simp [h]
              }
              apply (le_trans _ hle)
              apply tsum_le_tsum
              · intro x; apply mul_le_mul
                · linarith
                · exact (hr x)
                · unfold restr; simp
                · have h := (μ.2.2 x); simp [h, heq]
              · rw [heq]; apply convex_sum_summable
              · rw [heq]; apply convex_sum_summable
          · sorry -- This case (the reverse inclusion) is a lot harder
        }
    rw [he]
    exact isClosed_iInter (fun _ => closed_finitary_half_space)
  }

lemma isClosed_distr {α : Type} [DecidableEq α] :
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
instance {α : Type} [DecidableEq α] : CompactSpace (Distr α) := {
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
theorem chain_inter_nonempty {α : Type} [DecidableEq α] (c : ℕ → Set (Distr α)) :
  (∀ n : ℕ, c (n+1) ⊆ c n) →
  (∀ n : ℕ, IsClosed (c n) ∧ (c n).Nonempty) →
  (Set.iInter c).Nonempty := by {
    intro hc h
    apply (IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed c hc)
    · intro i; exact (h i).2
    · exact IsCompact.of_isClosed_subset CompactSpace.isCompact_univ (h 0).1 (Set.subset_univ (c 0))
    · intro i; exact (h i).1
  }
