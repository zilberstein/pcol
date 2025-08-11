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
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := Real.toNNReal ∘ μ.val ∘ WithBot.some

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

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} [DecidableEq α] (e : α → NNReal) (r : NNReal) :
  IsClosed { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } := by {
    have he :
      { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } =
      Set.iInter (fun s : Finset α =>
      -- TODO: simplify this proof with Summable.tsum_le_of_sum_le and sum_le_tsum
        { g : α → NNReal | ∑' x, g x * restr e s x ≤ r }) := by {
          ext g; simp; constructor
          · rintro ⟨hs, hb⟩ s
            have hle : ∀ x, (fun y => g y * restr e s y) x ≤ (fun y => g y * e y) x := by {
              intro x; simp [restr]; by_cases h : (x ∈ s); simp [h]; simp [h]
            }
            apply (le_trans _ hb)
            apply tsum_le_tsum
            · intro x; apply hle
            · apply summable_of_finite_support; simp; apply Set.Finite.inf_of_right; simp
            · exact hs
          · intro h
            have hhh : (∑' (x : α), ↑(g x * e x) : ENNReal) ≤ ↑r := by {
              rw [ENNReal.tsum_eq_iSup_sum]
              apply iSup_le_iff.2
              intro s
              have heq : ∀ x ∈ s, (fun x => (↑(g x * e x) : ENNReal)) x =
                                  (fun x => ↑(g x * restr e s x)) x := by {
                intro x hx; simp [restr, hx]
              }
              rw [Finset.sum_congr rfl heq]
              rw [← tsum_eq_sum]
              · rw [← ENNReal.coe_tsum]
                · simp [h]
                · apply summable_of_finite_support; simp; apply Set.Finite.inf_of_right; simp
              · intro x hx; simp [restr]; intro hx'; contradiction
            }
            have hs : Summable fun x ↦ g x * e x := by {
              apply ENNReal.tsum_coe_ne_top_iff_summable.1
              apply lt_top_iff_ne_top.1
              have ht : (↑r : ENNReal) < ⊤ := ENNReal.coe_lt_top
              exact lt_of_le_of_lt hhh ht
            }
            rw [← ENNReal.coe_tsum hs] at hhh; simp at hhh
            exact ⟨hs, hhh⟩
        }
    rw [he]
    exact isClosed_iInter (fun _ => closed_finitary_half_space)
  }

lemma isClosed_distr {α : Type} [DecidableEq α] :
  IsClosed { f : α → NNReal | Summable f ∧ tsum f ≤ 1 } := by {
    let const (_ : α) : NNReal := 1
    have heq (f : α → NNReal) : f = fun x => f x * const x := by ext x; simp [const]
    have h :
      { f : α → NNReal | Summable f ∧ tsum f ≤ 1 } =
      { f | Summable (fun x => f x * const x) ∧ ∑' x, f x * const x ≤ 1 } := by {
        ext f; simp; rw [← heq f]
      }
    rw [h]; exact (closed_infinitary_half_space const 1)
}

noncomputable def to_distr {α : Type} (f : α → NNReal) : WithBot α → ℝ :=
  fun x => match x with
    | none => ↑(1 - ∑' y : α, f y)
    | some y => ↑(f y)

lemma to_distr_sum {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
  HasSum (to_distr f) 1 := by {
    rcases h with ⟨r, hr⟩
    let g : α ⊕ PUnit.{1} → ℝ := to_distr f ∘ (Equiv.optionEquivSumPUnit α).invFun
    have hs : HasSum (g ∘ Sum.inl) r := by {
      have h : g ∘ Sum.inl = (↑) ∘ f := by ext x; simp [to_distr, g]
      rw [h]; exact NNReal.hasSum_coe.2 hr
    }
    have ht : tsum f = r := (Summable.hasSum_iff ⟨r, hr⟩).1 hr
    have hn : HasSum (g ∘ Sum.inr) (1 - r) := by {
      have h : g ∘ Sum.inr = fun _ => ↑(1 - r) := by ext x; simp [g, to_distr, ht]
      rw [h]
      have heq : (1 - ↑r : ℝ) = (fun (x : PUnit.{1}) ↦ ↑(1 - r)) default := by rw [ht] at h'; simp [h']
      rw [heq]; apply hasSum_unique
    }
    have hh := HasSum.sum hs hn
    simp [g] at hh
    exact (Equiv.hasSum_iff (Equiv.optionEquivSumPUnit α).symm).1 hh
  }

lemma dist_inj_sum_le_1 {α : Type} {μ : Distr α} :
  Summable (distr_inj μ) ∧ tsum (distr_inj μ) ≤ 1 := by {
  rcases μ with ⟨d, ⟨hs, hl⟩⟩; simp [distr_inj]
  have hsm := Summable.toNNReal (Summable.comp_injective ⟨1, hs⟩ (Option.some_injective α))
  constructor
  · exact hsm
  · have hs' := HasSum.toNNReal hl hs
    simp at hs'; rw [← (Summable.hasSum_iff ⟨1, hs'⟩).1 hs']
    apply tsum_le_tsum_of_inj some (Option.some_injective α)
    · simp
    · intro x; simp; apply le_refl
    · exact hsm
    · exact ⟨1, hs'⟩
}

lemma dist_invert {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
  ∃ μ : Distr α, distr_inj μ = f := by {
    let μ : Distr α := Subtype.mk (to_distr f) (by {
      constructor
      · exact to_distr_sum h h'
      · unfold to_distr; intro x; cases x; simp; simp
    })
    use μ; ext x; simp [μ, distr_inj, to_distr]
  }

lemma dist_decomp {α : Type} :
  Set.range distr_inj =
  { f : α → NNReal | ∀ x, f x ≤ 1 } ∩
  { f : α → NNReal | Summable f ∧ tsum f ≤ 1 } := by {
    ext f; constructor
    · rintro ⟨μ, hf⟩; constructor
      · intro x
        rw [← hf, distr_inj]; simp
        exact distr_upper_bound μ x
      · simp [← hf]; exact dist_inj_sum_le_1
    · simp [distr_inj]; intro hlu hs hb; exact dist_invert hs hb
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
