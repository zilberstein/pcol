import Init.Prelude
import Mathlib

open ENNReal

def Distr (α : Type) := PMF (WithBot α)

instance {α : Type} : FunLike (Distr α) (WithBot α) ENNReal where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.eq h

lemma distr_coe {α : Type} {μ : Distr α} {x : WithBot α} : μ x = μ.val x := rfl

@[ext]
theorem distr_ext {α : Type} {μ ν : Distr α} (h : ∀ x, μ x = ν x) : μ = ν := by {
    apply Subtype.ext; ext x; exact h x
  }

lemma distr_upper_bound {α : Type} (μ : Distr α) (x : WithBot α) :
  μ x ≤ 1 := by {
    rcases μ with ⟨d, hs⟩
    exact (le_hasSum hs x (fun _ _ => bot_le))
  }

lemma prob_bot {α : Type} (d : Distr α) : d ⊥ = 1 - ∑' x : α, d x := by {
  rw [← PMF.tsum_coe d]
  rw [ENNReal.tsum_eq_add_tsum_ite ⊥, Equiv.tsum_eq_tsum_of_support]
  · rw [ENNReal.add_sub_cancel_right]
    refine lt_top_iff_ne_top.mp ?_
    refine lt_of_le_of_lt ?_ (lt_of_le_of_ne le_top d.tsum_coe_ne_top)
    refine tsum_comp_le_tsum_of_injective ?_ ⇑d
    exact WithBot.coe_injective
  · constructor
    case toFun =>
      intro ⟨ x , h ⟩
      cases x
      · exfalso ; simp at *
      · exact ⟨ _ , by simp at * ;  assumption ⟩
    case invFun =>
      intro ⟨ x , h ⟩
      exact ⟨ ↑ x , by simp at * ; assumption ⟩
    case right_inv =>
      intros x
      simp at *
    case left_inv =>
      intro ⟨ x , h ⟩
      simp at *
      cases x
      · exfalso ; simp at *
      · simp
  · intro ⟨x, h⟩
    cases x
    · exfalso
      simp at *
    · simp
}

-- Inject a Distribution into α-dimensional Euclidean Space
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := ENNReal.toNNReal ∘ μ.val ∘ WithBot.some

lemma distr_inj_injective {α : Type} : @Function.Injective (Distr α) (α → NNReal) distr_inj := by {
  intro μ ν heq
  have h : ∀ x : α, μ x = ν x := by {
    intro x; unfold distr_inj at heq; simp [distr_coe]
    have hnt (ξ : Distr α) : tsum ξ.val ≠ ⊤ := by simp [HasSum.tsum_eq ξ.2]
    have hbot ξ := ENNReal.ne_top_of_tsum_ne_top (hnt ξ) (WithBot.some x)
    apply (ENNReal.toNNReal_eq_toNNReal_iff' (hbot μ) (hbot ν)).1 (congrFun heq x)
  }
  ext x; match x with
  | ⊥ => simp [prob_bot, tsum_congr h]
  | WithBot.some y => exact h y
}

-- Topology on distributions is the product of Euclidean topologies
instance {α : Type} : TopologicalSpace (Distr α) :=
  TopologicalSpace.induced distr_inj Pi.topologicalSpace

instance {α : Type} : T1Space (Distr α) where
  t1 μ := by {
    have hi := (Topology.isInducing_iff (@distr_inj α)).2 (by rfl)
    apply (Topology.IsInducing.isClosed_iff hi).2
    use {distr_inj μ}; constructor
    · exact isClosed_singleton
    · unfold Set.preimage; ext ν; simp
      refine ⟨?_, congrArg _⟩
      intro h; exact distr_inj_injective h
  }

-- Based on Lemma B.4.2 of MM'05, except we use the fact that { x | f x ≤ r } is closed
-- for any continuous function f instead of using projections
lemma closed_finitary_half_space {α : Type} {e : α → NNReal} {r : NNReal} (s : Finset α) :
  IsClosed { d : α → NNReal | (∑ x ∈ s, d x * e x) ≤ r } := by {
    have hcf : Continuous fun (d : α → NNReal) => ∑ x ∈ s, d x * e x :=
      continuous_finset_sum s fun x _ => Continuous.mul (continuous_apply x) continuous_const
    exact isClosed_le hcf continuous_const
  }

-- Infinitary half-space is equal to the intersection of all related finitary half-spaces
lemma infinitary_half_space_fin_approx {α : Type} (e : α → NNReal) (r : NNReal) :
  { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } =
  ⋂ (s : Finset α), { g : α → NNReal | ∑ x ∈ s, g x * e x ≤ r } := by {
    ext d; simp
    have he :
      Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r ↔
      (∑' x, (↑(d x * e x) : ENNReal)) ≤ ↑r := by {
      constructor
      · rintro ⟨hs, hb⟩; rw [← ENNReal.coe_tsum hs]; exact ENNReal.coe_le_coe.2 hb
      · intro hb
        have hs :=
          ENNReal.tsum_coe_ne_top_iff_summable.1 (lt_top_iff_ne_top.1 (lt_of_le_of_lt hb ENNReal.coe_lt_top))
        rw [← ENNReal.coe_tsum hs] at hb; exact ⟨hs, ENNReal.coe_le_coe.1 hb⟩
    }
    rw [he, ENNReal.tsum_eq_iSup_sum, iSup_le_iff]
    apply forall_congr'; intro s; rw [← ENNReal.coe_finset_sum]; exact ENNReal.coe_le_coe
  }

-- Lemma B.4.3 of MM'05
lemma closed_infinitary_half_space {α : Type} (e : α → NNReal) (r : NNReal) :
  IsClosed { d : α → NNReal | Summable (fun x => d x * e x) ∧ ∑' x, d x * e x ≤ r } := by
    rw [infinitary_half_space_fin_approx]; exact isClosed_iInter closed_finitary_half_space

noncomputable def to_distr {α : Type} (f : α → NNReal) : WithBot α → ENNReal :=
  fun x => match x with
    | none => ↑(1 - ∑' y : α, f y)
    | some y => ↑(f y)

lemma to_distr_sum {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
  HasSum (to_distr f) 1 := by {
    rcases h with ⟨r, hr⟩
    let g : α ⊕ PUnit.{1} → ENNReal := to_distr f ∘ (Equiv.optionEquivSumPUnit α).invFun
    have hs : HasSum (g ∘ Sum.inl) r := by {
      have h : g ∘ Sum.inl = (↑) ∘ f := by ext x; simp [to_distr, g]
      rw [h]; exact ENNReal.hasSum_coe.2 hr
    }
    have ht : tsum f = r := (Summable.hasSum_iff ⟨r, hr⟩).1 hr
    have hn : HasSum (g ∘ Sum.inr) (1 - r) := by {
      have h : g ∘ Sum.inr = fun _ => ↑(1 - r) := by ext x; simp [g, to_distr, ht]
      rw [h]; apply hasSum_unique
    }
    have hh := HasSum.sum hs hn
    rw [add_comm,
        ENNReal.sub_add_eq_add_sub _ ENNReal.coe_ne_top,
        ENNReal.add_sub_cancel_right ENNReal.coe_ne_top] at hh
    · simp [g] at hh; exact (Equiv.hasSum_iff (Equiv.optionEquivSumPUnit α).symm).1 hh
    · rw [← HasSum.tsum_eq hr]; exact ENNReal.coe_le_coe_of_le h'
  }

lemma dist_inj_sum_le_1 {α : Type} {μ : Distr α} : Summable (distr_inj μ) ∧ tsum (distr_inj μ) ≤ 1 := by {
  rcases μ with ⟨d, hs⟩; simp [distr_inj]
  have hnt : tsum d ≠ ⊤ := by simp [HasSum.tsum_eq hs]
  have hs₁ : HasSum (ENNReal.toNNReal ∘ d) 1 := by {
    apply (Summable.hasSum_iff (ENNReal.summable_toNNReal_of_tsum_ne_top hnt)).2
    simp; rw [← ENNReal.tsum_toNNReal_eq (ENNReal.ne_top_of_tsum_ne_top hnt)]
    exact (ENNReal.toNNReal_eq_one_iff _).2 (HasSum.tsum_eq hs)
  }
  have hsm : Summable (distr_inj ⟨d, hs⟩) := by {
    apply NNReal.summable_coe.1
    have hs₂ : HasSum (NNReal.toReal ∘ ENNReal.toNNReal ∘ d) 1 := by
      rw [← NNReal.coe_one]; exact NNReal.hasSum_coe.2 hs₁
    apply Summable.comp_injective ⟨1, hs₂⟩ WithBot.coe_injective
  }
  constructor
  · exact hsm
  · rw [← Function.comp_assoc, ← HasSum.tsum_eq hs₁]
    apply tsum_le_tsum_of_inj some (Option.some_injective α) (by simp) _ hsm ⟨1, hs₁⟩
    simp [distr_inj]; intro x; have hx := ENNReal.ne_top_of_tsum_ne_top hnt (WithBot.some x)
    exact (ENNReal.toNNReal_le_toNNReal hx hx).2 (le_refl _)
}

lemma dist_invert {α : Type} {f : α → NNReal} (h : Summable f) (h' : tsum f ≤ 1) :
  ∃ μ : Distr α, distr_inj μ = f := by {
    have hl (x : WithBot α) : 0 ≤ to_distr f x := by unfold to_distr; cases x; simp; simp
    let μ : Distr α := Subtype.mk (to_distr f) (to_distr_sum h h')
    use μ; ext x; simp [μ, distr_inj, to_distr]
  }

-- The space of distributions can be decomposed as follows:
--   Distr α = [0, 1]^α ∩ { f : α → NNReal | tsum f ≤ 1 }
lemma dist_decomp {α : Type} :
  let e (_ : α): NNReal := 1
  Set.range distr_inj =
  { f : α → NNReal | ∀ x, f x ∈ Set.Icc 0 1 } ∩
  { f : α → NNReal | Summable (fun x => f x * e x) ∧ ∑' x, f x * e x ≤ 1 } := by {
    ext f; constructor
    · rintro ⟨μ, hf⟩; constructor
      · intro x; rw [← hf, distr_inj]; simp
        rw [← ENNReal.one_toNNReal]
        apply (ENNReal.toNNReal_le_toNNReal _ _).2
        · exact distr_upper_bound μ x
        · exact ne_top_of_le_ne_top (by simp) (distr_upper_bound μ x)
        · simp
      · simp [← hf]; exact dist_inj_sum_le_1
    · simp [distr_inj]; intro hlu hs hb; exact dist_invert hs hb
  }

-- Lemma B.4.4 of MM'05
instance {α : Type} : CompactSpace (Distr α) := {
  isCompact_univ := by {
    have hi := (Topology.isInducing_iff (@distr_inj α)).2 (by rfl)
    apply (Topology.IsInducing.isCompact_iff hi).2
    -- Distr α = [0, 1]^α ∩ { f : α → NNReal | tsum f ≤ 1 }
    simp; rw [dist_decomp]
    -- The set above is the intersection of a compact set and a closed set, so it is compact
    apply IsCompact.inter_right
      -- [0, 1]^α is compact by Tychonoff's Theorem
    · exact isCompact_pi_infinite fun _ => isCompact_Icc
      -- Infinitary half-space is closed
    · exact closed_infinitary_half_space _ 1
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

noncomputable def distr_bind {α β : Type} (s : Set (Distr α)) (k : α → Set (Distr β)) : Set (Distr β) :=
  ⋃ μ ∈ s, ⋃ f ∈ μ.support.pi (Option.elim · Set.univ k), { PMF.bind μ f }
--  { f : WithBot α → Distr β | ∀ x : α, ↑x ∈ μ.support → f x ∈ k x },


lemma bind_closed {α β : Type} {s : Set (Distr α)} {k : α → Set (Distr β)} (h : ∀ x : α , IsClosed (k x)) :
  IsClosed (distr_bind s k) := by {
    have hi := (Topology.isInducing_iff (@distr_inj β)).2 (by rfl)
    apply (Topology.IsInducing.isClosed_iff hi).2
    use (distr_inj <$> distr_bind s k)
    refine ⟨?_, Function.Injective.preimage_image distr_inj_injective _⟩
    · unfold distr_bind; simp [Set.image_iUnion]
      sorry
  }
