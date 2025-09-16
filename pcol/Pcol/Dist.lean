import Init.Prelude
import Mathlib

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
    refine ENNReal.tsum_comp_le_tsum_of_injective ?_ ⇑d
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

lemma prob_not_bot {α : Type} (d : Distr α) : ∑' x : α, d x = 1 - d ⊥ := by
  rw [prob_bot]; refine Eq.symm (ENNReal.sub_sub_cancel ENNReal.one_ne_top ?_)
  rw [← PMF.tsum_coe d]
  exact tsum_le_tsum_of_inj some (Option.some_injective _)
    (fun _ _ ↦ bot_le)
    (fun _ ↦ le_refl _)
    ENNReal.summable
    ENNReal.summable

-- Inject a Distribution into α-dimensional Euclidean Space
def distr_inj {α : Type} (μ : Distr α) : α → NNReal := ENNReal.toNNReal ∘ μ ∘ WithBot.some

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

lemma distr_inducing {α : Type} : @Topology.IsInducing (Distr α) (α → NNReal) _ _ distr_inj :=
  (Topology.isInducing_iff (@distr_inj α)).2 (by rfl)

instance {α : Type} : T1Space (Distr α) where
  t1 μ := by {
    apply distr_inducing.isClosed_iff.2
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
    use μ; ext x; simp [μ, distr_inj, to_distr, distr_coe]
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
    apply distr_inducing.isCompact_iff.2
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

lemma prob_not_top {α : Type} {μ : Distr α} {x : WithBot α} : μ x ≠ ⊤ := by {
  rw [distr_coe]; apply ENNReal.ne_top_of_tsum_ne_top; simp [HasSum.tsum_eq μ.2]
}

noncomputable def distr_bind {α β : Type} (s : Set (Distr α)) (k : α → Set (Distr β)) : Set (Distr β) :=
  Function.uncurry PMF.bind '' ⋃ μ ∈ s, {μ} ×ˢ μ.support.pi (Option.elim · Set.univ k)
--  { f : WithBot α → Distr β | ∀ x : α, ↑x ∈ μ.support → f x ∈ k x },

-- The image of PMF.bind is the same over the following two sets:
--   { (μ, f) | μ ∈ s ∧ ∀ x ∈ μ.support, f x ∈ k x }
--   AND
--   s × { f | ∀ x, f x ∈ k x }
-- Which is useful, since the latter set is compact
lemma distr_bind_image {α β : Type} {s : Set (Distr α)} {k : α → Set (Distr β)}
  (hne : ∀ x, (k x).Nonempty) :
  distr_bind s k = Function.uncurry PMF.bind '' (s ×ˢ Set.univ.pi (Option.elim · Set.univ k)) := by {
    ext ν; constructor
    · rintro ⟨⟨μ, f⟩, hmem, hν⟩
      simp at hmem; rcases hmem with ⟨hmem, hμ⟩
      have h : ∀ (x : WithBot α), ∃ y, y ∈ (Option.elim · Set.univ k) x ∧ (x ∈ μ.support → y = f x) := by {
        intro x; by_cases h : x ∈ μ.support
        · exact ⟨f x, hmem x h, fun _ => rfl⟩
        · match x with
          | ⊥ => refine ⟨PMF.pure ⊥, by simp [Option.elim], fun hc => False.elim (h hc)⟩
          | WithBot.some z =>
            rcases (hne z) with ⟨y, hy⟩
            refine ⟨y, ?_, fun hc => False.elim (h hc)⟩
            simp [Option.elim]; exact hy
      }
      choose g hg using h
      simp; refine ⟨μ, hμ, g, ?_, ?_⟩
      · intro x; exact (hg x).1
      · simp at hν; rw [← hν]
        unfold PMF.bind; ext z; simp [distr_coe]
        refine tsum_congr ?_
        intro x; by_cases hx : x ∈ μ.support
        · rw [(hg x).2 hx]
        · simp at hx; rw [hx]; simp
    -- The reverse direction is immediate
    · rintro ⟨⟨μ, f⟩, hmem, hν⟩
      simp at hmem; rcases hmem with ⟨hμ, hf⟩
      simp [distr_bind]; refine ⟨μ, f, ⟨hμ, fun x _ => hf x⟩, ?_⟩
      · simp at hν; exact hν
  }

lemma exits_finsum_within {α β : Type} {d : Distr α} {k : WithBot α → Distr β} {l u : ℝ} {y : β}
    (hlt : l < u) (hsum : (∑' x, (d x).toReal * (k x y).toReal) ∈ Set.Ioo l u) :
    ∃ ε > 0, ∃ F : Finset (WithBot α), (∑ x ∈ F, (d x).toReal * (k x y).toReal) ∈ Set.Ioo (l + ε) (u - ε) := by
  have hsm : Summable fun x => (d x).toReal * (k x y).toReal := by sorry
  let ε : ℝ := ((∑' x, (d x).toReal * (k x y).toReal) - l) / 2
  rcases hsum with ⟨hl, hu⟩
  have hε : ε > 0 := by unfold ε; linarith
  have htends := (Metric.tendsto_nhds.mp hsm.hasSum ε hε).exists; obtain ⟨F, hF⟩ := htends
  refine ⟨ε, hε, F, ?_⟩
  sorry

-- Based on Lemma B.3 of the POPL '25 paper. Original Proof due to Dexter Kozen
lemma distr_bind_tsum_continuous {α β : Type} {y : β} :
    @Continuous (Distr α × (WithBot α → Distr β)) Real _ _
      (fun d ↦ ∑' x, (d.1 x * d.2 x y).toReal) := by {
  refine Real.isTopologicalBasis_Ioo_rat.continuous_iff.mpr ?_
  intro s hs
  simp at hs; rcases hs with ⟨l, u, hlt, hs⟩; subst hs
  refine isOpen_iff_mem_nhds.mpr ?_
  simp; intro d k hl hu; refine mem_nhds_iff.mpr ?_
  --
  rcases exits_finsum_within (Rat.cast_lt.mpr hlt) (Set.mem_Ioo.mpr ⟨hl, hu⟩) with ⟨ε, hε, F, ⟨hFl, hFu⟩⟩
  --

  let δ := ε / (4 * F.card)
  have hδ : (2*δ + δ^2) * F.card < ε := by unfold δ; sorry
  let U := { μ : Distr α | ∀ x ∈ F, (μ x).toReal ∈ Set.Ioo ((d x).toReal - ε) ((d x).toReal + ε)}
  -- Alternatively, add [DecidableEq α] to context
  have _ x := Classical.dec (x ∈ F)
  let V x := if x ∈ F then { ν : Distr β | (ν y).toReal ∈ Set.Ioo ((k x y).toReal - δ) ((k x y).toReal + δ)} else Set.univ
  refine ⟨U ×ˢ F.toSet.pi V, ?_, ?_, ?_⟩
  · intro ⟨μ, f⟩; simp [U, V]; intro hu hv; constructor
    · have hll : l = l + ε - ε := by { linarith } ; rw [hll]
      refine ((sub_lt_sub_iff_right _).mpr hFl).trans ?_
      refine (sub_lt_sub_left hδ _).trans ?_
      have hcr : (2 * δ + δ ^ 2) * F.card = F.card • (2 * δ + δ ^ 2) := by rw [mul_comm]; sorry
      rw [hcr, ← (sub_right_inj (G := ℝ)).mpr (Finset.sum_const (β := ℝ) _), ← Finset.sum_sub_distrib]
      sorry
    · sorry
  · refine IsOpen.prod (isOpen_induced_iff.mpr ⟨distr_inj '' U, ?_, ?_⟩) ?_
    · simp [distr_inj, U, Set.image]; refine isOpen_pi_iff.mpr ?_; intro f hf
      simp at hf; rcases hf with ⟨μ, hμ⟩
      refine ⟨F.filterMap id ?_, sorry, ?_, ?_⟩
      · intro a b c; simp; intro ha hb; subst ha hb; rfl
      · intro x hx; sorry
      · sorry
    · exact Set.preimage_image_eq _ distr_inj_injective
    · refine isOpen_set_pi (Finset.finite_toSet _) ?_
      intro x hx; unfold V; apply Finset.mem_coe.mp at hx; simp [hx]
      sorry
  · simp [U, V]; refine ⟨fun _ _ ↦ hε, ?_⟩
    intro _ _; unfold δ; refine div_pos hε ?_; sorry
}

lemma distr_bind_continuous {α β : Type} :
  @Continuous (Distr α × (WithBot α → Distr β)) (β → NNReal) _ _
  (distr_inj ∘ Function.uncurry PMF.bind) := by {
    refine continuous_pi ?_; intro y
    simp [distr_inj, Function.uncurry]
    refine ContinuousOn.comp_continuous ENNReal.continuousOn_toNNReal ?_ (fun _ => prob_not_top)
    -- Now, show that the infinite sum is continuous
    simp [PMF.bind, distr_coe]
    refine Continuous.congr ?_
      (fun d => Eq.trans (congrArg _ (Eq.symm (ENNReal.tsum_toReal_eq ?_))) (ENNReal.ofReal_toReal ?_))
    · refine Continuous.comp ENNReal.continuous_ofReal distr_bind_tsum_continuous (g := ENNReal.ofReal)
    · intro d; exact ENNReal.mul_ne_top prob_not_top prob_not_top
    · refine ne_top_of_le_ne_top d.1.tsum_coe_ne_top ?_
      refine tsum_le_tsum ?_ ENNReal.summable ENNReal.summable
      intro x
      exact le_trans (b := d.1 x * 1) (mul_le_mul (le_refl _) (distr_upper_bound _ _) bot_le bot_le) (by simp)
  }

-- Lemma B.3 of Zilberstein et al. POPL'25
lemma bind_closed {α β : Type} {s : Set (Distr α)} {k : α → Set (Distr β)}
  (hcs : IsClosed s)
  (hne : ∀ x : α , (k x).Nonempty)
  (h : ∀ x : α , IsClosed (k x)) :
  IsClosed (distr_bind s k) := by {
    -- Move into the product topology NNReal^α
    refine distr_inducing.isClosed_iff.2 ⟨distr_inj '' distr_bind s k, ?_⟩
    refine ⟨?_, Function.Injective.preimage_image distr_inj_injective _⟩
    rw [distr_bind_image hne, ← Set.image_comp]
    -- Any compact set is closed, since we are working in a compact space
    have hx (x : WithBot α) : IsClosed (Option.elim x Set.univ k) := by {
      match x with
      | ⊥ => simp [Option.elim]
      | WithBot.some y => simp [Option.elim]; exact h y
    }
    have hc : IsCompact (Set.prod s (Set.univ.pi (Option.elim · Set.univ k))) :=
      IsClosed.isCompact (IsClosed.prod hcs (isClosed_set_pi fun x _ => hx x))
    -- The image of a continuous function in a Hausdorff space is closed
    exact IsCompact.isClosed (hc.image distr_bind_continuous)
  }
