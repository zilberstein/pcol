import Init.Prelude
import Mathlib

def Distr (α : Type) := { μ : WithBot α → ℝ // HasSum μ 1 ∧ ∀x, 0 ≤ μ x }

instance {α : Type} : FunLike (Distr α) (WithBot α) ℝ where
  coe d := d.1
  coe_injective' _ _ h := Subtype.eq h

def supp {α : Type} (μ : Distr α) : Set (WithBot α) := { x | μ x ≠ 0 }

lemma distr_upper_bound {α : Type} (μ : Distr α) (x : WithBot α) :
  μ x ≤ 1 := by {
    rcases μ with ⟨d, ⟨hs, hl⟩⟩
    exact (le_hasSum hs x (fun y _ => hl y))
  }

-- Inject a Distribution into α-dimensional Euclidean Space
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := Real.toNNReal ∘ μ ∘ WithBot.some

instance {α : Type} : TopologicalSpace (Distr α) :=
  TopologicalSpace.induced distr_inj Pi.topologicalSpace

lemma unit_interval_compact : IsCompact { r : NNReal | r ≤ 1 } := by {
  have h : { r : NNReal | r ≤ 1 } = Metric.closedBall 0.5 0.5 := by {
    have h1 : (0.5 + 0.5 : ℝ) = ↑(1 : NNReal) := by rw [NNReal.coe_one]; linarith
    ext r; constructor
    · simp; intro hu
      rw [NNReal.dist_eq]
      apply abs_le'.2; apply NNReal.coe_le_coe.2 at hu; constructor
      · simp; rw [h1]; exact hu
      · simp
    · intro hr; simp at hr
      rw [NNReal.dist_eq] at hr; apply abs_le'.1 at hr
      rcases hr with ⟨hr, _⟩; simp at hr; rw [h1] at hr
      exact (NNReal.coe_le_coe.2 hr)
  }
  apply Metric.isCompact_iff_isClosed_bounded.2
  constructor
  · rw [h]; exact Metric.isClosed_closedBall
  · use { r : ℝ | 1 < r ∨ r < 0}; constructor
    · simp; constructor
      · use -1; intro x hx; right; linarith
      · use 2; intro x hx; left; linarith
    · rintro ⟨r, hr⟩ hs ht; cases hs with
      | inl h1 => simp at h1; simp at ht; apply NNReal.coe_le_coe.2 at ht; simp at ht; linarith
      | inr h2 => simp at h2; linarith
}


noncomputable def restr {α : Type} [DecidableEq α] (f : α → NNReal) (s : Finset α) : α →₀ NNReal :=
  Finsupp.mk
    { x ∈ s | f x ≠ 0 }
    (fun x => if x ∈ s then f x else 0)
    (by simp)

-- Lemma B.4.2 of MM'05
lemma closed_finitary_half_space {α : Type} {e : α →₀ NNReal} {r : NNReal} :
  IsClosed { d : α → NNReal | (∑' x, d x * e x) ≤ r } := by {
    let f (d : α → NNReal) : NNReal := ∑ x ∈ e.support, d x * e x
    let g (_ : α → NNReal) : NNReal := r
    have heq : { d : α → NNReal | (∑' x, d x * e x) ≤ r } = { d | f d ≤ g d } := by {
      ext d; simp
      have hf : (Function.support fun x ↦ d x * e x) ⊆ e.support := by simp
      rw [tsum_eq_sum' hf]
    }
    have hcf : Continuous f := by {
      apply continuous_finset_sum; intro x hx
      exact Continuous.mul (continuous_apply x) continuous_const
    }
    rw [heq]
    exact isClosed_le hcf continuous_const
  }

-- lemma hasSum_toNNReal {α : Type} {f : α → ENNReal} (hsum : ∑' x, f x ≠ ⊤) :
--     HasSum (fun x => (f x).toNNReal) (∑' x, (f x).toNNReal) := by
--   lift f to α → NNReal using ENNReal.ne_top_of_tsum_ne_top hsum
--   simp only [← NNReal.coe_tsum, NNReal.hasSum_coe]
--   exact (tsum_coe_ne_top_iff_summable.1 hsum).hasSum

lemma summable_bounded {α : Type} {r : NNReal} {f : α → NNReal} (h : ∑' x : α, f x ≤ r) :
  Summable f := by {
    apply ENNReal.tsum_coe_ne_top_iff_summable.1
    have heq : (↑(∑' (x : α), f x) : ENNReal) = ∑' (b : α), ↑(f b) := by {
      sorry
    }
    rw [← heq]
    exact ENNReal.coe_ne_top
  }

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} [DecidableEq α] (e : α → NNReal) (r : NNReal) :
  IsClosed { d : α → NNReal | ∑' x, d x * e x ≤ r } := by {
    have he :
      { g : α → NNReal | ∑' x, g x * e x ≤ r } =
      Set.iInter (fun s : Finset α =>
        { g : α → NNReal | ∑' x, g x * restr e s x ≤ r }) := by {
          ext g; simp; constructor
          · intro hb s
            have hle : ∀ x, (fun y => g y * restr e s y) x ≤ (fun y => g y * e y) x := by {
              intro x; simp [restr]; by_cases h : (x ∈ s); simp [h]; simp [h]
            }
            apply (le_trans _ hb)
            apply tsum_le_tsum
            · intro x; apply hle
            · apply summable_of_finite_support; simp; apply Set.Finite.inf_of_right; simp
            · exact (summable_bounded hb)
          · intro h
            sorry -- This case (the reverse inclusion) is a lot harder
        }
    rw [he]
    exact isClosed_iInter (fun _ => closed_finitary_half_space)
  }

lemma isClosed_distr {α : Type} [DecidableEq α] :
  IsClosed { f : α → NNReal | (∑' x : α, f x) ≤ 1 } := by {
    let const (_ : α) : NNReal := 1
    have heq (f : α → NNReal) : (fun x => f x) = fun x => f x * const x := by ext x; simp [const]
    have h :
      { f : α → NNReal | (∑' x : α, f x) ≤ 1 } =
      { f | ∑' x, f x * const x ≤ 1 } := by {
        ext f; simp; rw [heq]
      }
    rw [h]; exact (closed_infinitary_half_space const 1)
}

lemma dist_decomp {α : Type} :
  Set.range distr_inj =
  { f : α → NNReal | ∀ x, f x ≤ 1 } ∩
  { f : α → NNReal | (∑' x : α, f x) ≤ 1 } := by {
    ext f; constructor
    · rintro ⟨⟨g, ⟨hs, hl⟩⟩, hf⟩; constructor
      · intro x
        rw [← hf, distr_inj]; simp
        exact distr_upper_bound ⟨g, ⟨hs, hl⟩⟩ x
      · simp [← hf, distr_inj]
        have h := (Summable.hasSum_iff ⟨1, hs⟩).1 hs
        apply (congrArg Real.toNNReal) at h
        rw [Real.toNNReal_one] at h
        rw [← h]
        unfold Real.toNNReal at h
        sorry
        -- rw [NNReal.coe_tsum_of_nonneg hl] at h
        -- let g' (x : WithBot α) : NNReal := ⟨g x, hl x⟩
        -- let hg : (fun x => g x) = fun x => ↑(g' x) := by simp [g']
        -- rw [hg]; rw [← NNReal.tsum_eq_toNNReal_tsum]
    · simp [distr_inj]; intro hlu hs; sorry
  }

-- Lemma B.4.4 of MM'05
instance {α : Type} [DecidableEq α] : CompactSpace (Distr α) := {
  isCompact_univ := by {
    have hi := (Topology.isInducing_iff (@distr_inj α)).2 (by rfl)
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
