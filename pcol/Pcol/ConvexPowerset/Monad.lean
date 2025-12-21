import Pcol.ConvexPowerset
import Pcol.Dist

lemma c_pure_valid {α : Type} {x : α} : is_valid_C { PMF.pure (WithBot.some x) } := by
  constructor
  . simp
  · simp; exact convex_singleton _
  · exact isClosed_singleton
  · unfold IsUpperSet; simp; intro μ ν hle hμ
    rw [← hμ]; symm; apply proper_dist_maximal _ hle
    rw [hμ, PMF.pure_apply_of_ne]; simp

lemma c_bind_nonempty {α β : Type} {s : C α} {k : α → C β} :
    (distr_bind s.val (Subtype.val ∘ k)).Nonempty := by
  rcases s with ⟨s, hv⟩; unfold distr_bind
  rcases hv.nonempty with ⟨μ, hμ⟩
  let g t := Option.elim t Set.univ (Subtype.val ∘ k)
  have hf : (μ.support.pi g).Nonempty := by {
    apply (Set.pi_nonempty_iff (s := μ.support) (t := g)).2
    intro x; match x with
    | ⊥ => use ⊥; intro hb; simp [g, Option.elim]
    | WithBot.some y =>
        let u := k y
        rcases hk : (k y) with ⟨t, ⟨⟨ν, hν⟩, _⟩⟩; use ν; intro hy
        simp [g, Option.elim, hk, hν]
  }
  rcases hf with ⟨f, hf⟩; use (PMF.bind μ f); simp; use μ; use f
  refine ⟨⟨hμ, ?_⟩, rfl⟩
  intro x hx; unfold g at hf; exact Set.mem_pi.1 hf x hx

-- Lemma B.1 from. POPL '25
lemma countably_convex' {ι α : Type} {s : C α} {ξ : PMF ι} {f : ι → Distr α}
    (h : ∀ i ∈ ξ.support, f i ∈ s) : PMF.bind ξ f ∈ s := by sorry

namespace Distr

lemma convex_hassum_1 {α : Type} {d₁ d₂ : α → ENNReal} {p q : ENNReal}
    (h₁ : HasSum d₁ 1) (h₂ : HasSum d₂ 1) (h : p + q = 1) : HasSum (p • d₁ + q • d₂) 1 := by
  have hr (r : ENNReal) : r = r • 1 := by simp
  rw [← h]; refine HasSum.add ?_ ?_
  · nth_rewrite 2 [hr p]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    simp; rw [ENNReal.tsum_mul_left, HasSum.tsum_eq h₁]; simp
  · nth_rewrite 2 [hr q]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    simp; rw [ENNReal.tsum_mul_left, HasSum.tsum_eq h₂]; simp

noncomputable def convex_sum {α : Type} (μ ν : Distr α) (p q : ENNReal) (h : p + q = 1) : Distr α :=
  ⟨ p • μ.val + q • ν.val, convex_hassum_1 μ.property ν.property h ⟩

lemma convex_sum_0_left {α : Type} {μ ν : Distr α} {q : ENNReal} {h : 0 + q = 1} :
    convex_sum μ ν 0 q h = ν := by
  unfold convex_sum; simp at h; subst h; simp

lemma convex_sum_0_right {α : Type} {μ ν : Distr α} {p : ENNReal} {h : p + 0 = 1} :
    convex_sum μ ν p 0 h = μ := by
  unfold convex_sum; simp at h; subst h; simp

end Distr

-- Lemma B.1 from POPL '25
lemma c_bind_convex {α β : Type} {s : C α} {k : α → C β} :
    Convex ENNReal (Subtype.val '' distr_bind s.val (Subtype.val ∘ k)) := by
  simp [distr_bind, Set.image]
  rintro d₁ ⟨hs₁, μ, f, ⟨_, hμ, _, hf, _, _⟩, heq₁⟩
  rintro d₂ ⟨hs₂, ν, g, ⟨_, hν, _, hg, _, _⟩, heq₂⟩
  intro p q hp hq hsum
  let ξ := Distr.convex_sum μ ν p q hsum
  have hdsum x (h : x ∈ ξ.support) : (p * μ x / ξ x) + (q * ν x / ξ x) = 1 := by
    simp [ξ, Distr.convex_sum, DFunLike.coe]; rw [← ENNReal.add_div]
    refine ENNReal.div_self h (ne_top_of_le_ne_top ENNReal.one_ne_top ?_)
    nth_rewrite 3 [← hsum]; refine add_le_add ?_ ?_
    · refine LE.le.trans (mul_le_mul (le_refl _) (distr_upper_bound _ _) bot_le bot_le) ?_; simp
    · refine LE.le.trans (mul_le_mul (le_refl _) (distr_upper_bound _ _) bot_le bot_le) ?_; simp
  let d x (h : x ∈ ξ.support) := Distr.convex_sum (f x) (g x) _ _ (hdsum x h)
  have hr x : ∃ d', ∀ h : x ∈ ξ.support, d' = d x h := by
    by_cases hx : x ∈ ξ.support
    · exact ⟨d x hx, fun _ ↦ rfl⟩
    · exact ⟨⊥, fun hc ↦ False.elim (hx hc)⟩
  choose f' hf' using hr
  refine ⟨?_, ξ, f', ⟨ξ, ?_, f', ?_, rfl⟩, ?_⟩
  · exact Distr.convex_hassum_1 hs₁ hs₂ hsum
  · have h1 := (Set.mem_image Subtype.val _ _).mpr ⟨μ, hμ, rfl⟩
    have h2 := (Set.mem_image Subtype.val _ _).mpr ⟨ν, hν, rfl⟩
    have h := s.property.convex h1 h2 hp hq hsum
    obtain ⟨ξ', hξ, heq⟩ := (Set.mem_image Subtype.val s.val ξ.val).mp h
    apply Subtype.ext at heq; subst heq; exact hξ
  · intro x hx; rw [hf' x hx]; cases x with
    | bot => exact Set.mem_univ _
    | coe x =>
      simp [Option.elim]; simp [ξ, Distr.convex_sum, DFunLike.coe] at hx
      by_cases hμx : μ x = 0
      · unfold d; simp [hμx]
        have hνx := (hx (Or.inr hμx)).2
        rw [Distr.convex_sum_0_left]; exact hg x hνx
      · by_cases hνx : ν x = 0
        · unfold d; simp [hνx]; rw [Distr.convex_sum_0_right]; exact hf x hμx
        · unfold d; unfold Distr.convex_sum
          have h1 := (Set.mem_image Subtype.val _ _).mpr ⟨f x, hf _ hμx, rfl⟩
          have h2 := (Set.mem_image Subtype.val _ _).mpr ⟨g x, hg _ hνx, rfl⟩
          have h := (k x).property.convex h1 h2 bot_le bot_le (hdsum x (by {
            simp [ξ, Distr.convex_sum, DFunLike.coe]; exact hx
          }))
          obtain ⟨ξ', hξ, heq⟩ := (Set.mem_image Subtype.val _ _).mp h
          simp_rw [← heq]; exact hξ
  · ext z; rw [PMF.bind_apply]
    have h1 := congrArg Subtype.val heq₁; simp at h1; subst h1
    have h2 := congrArg Subtype.val heq₂; simp at h2; subst h2
    simp [PMF.bind, DFunLike.coe]
    rw [← ENNReal.tsum_mul_left, ← ENNReal.tsum_mul_left, ← tsum_add]
    refine tsum_congr fun x ↦ ?_; by_cases hξ : x ∈ ξ.support
    · rw [hf' _ hξ]; simp [d, Distr.convex_sum, DFunLike.coe]
      rw [ENNReal.div_eq_inv_mul, ENNReal.div_eq_inv_mul]
      rw [mul_assoc, mul_assoc, mul_assoc, ← mul_add, ← mul_assoc]
      rw [ENNReal.mul_inv_cancel]
      · simp [mul_assoc]
      · exact hξ
      · exact ne_top_of_le_ne_top ENNReal.one_ne_top (distr_upper_bound _ _)
    · simp at hξ; rw [distr_coe] at hξ; rw [hξ]
      simp [ξ, Distr.convex_sum] at hξ
      rcases hξ with ⟨hp | hμx, hq | hνx⟩
      · subst hp; subst hq; simp
      · subst hp; rw [hνx]; simp
      · rw [hμx]; subst hq ; simp
      · rw [hμx, hνx]; simp
    · exact ENNReal.summable
    · exact ENNReal.summable

lemma c_bind_closed {α β : Type} {s : C α} {k : α → C β} :
    IsClosed (distr_bind s.val (Subtype.val ∘ k)) := by
  apply bind_closed s.2.closed
  · intro x; simp [(k x).property.nonempty]
  · intro x; simp [(k x).property.closed]

-- For some reason, the Mathlib version is only for sums indexed by ℕ
theorem tsum_sub' {ι : Type} {f : ι → ENNReal} {g : ι → ENNReal} (h₁ : ∑' i, g i ≠ ⊤) (h₂ : g ≤ f) :
    ∑' i, (f i - g i) = ∑' i, f i - ∑' i, g i :=
  have : ∀ i, f i - g i + g i = f i := fun i => tsub_add_cancel_of_le (h₂ i)
  ENNReal.eq_sub_of_add_eq h₁ <| by simp only [← ENNReal.tsum_add, this]

lemma bind_toReal {α β : Type} {μ : Distr α} {f : WithBot α → Distr β} {y : WithBot β} :
    (μ.bind f y).toReal = ∑' x, (μ x).toReal * (f x y).toReal := by
  rw [PMF.bind_apply]; refine (ENNReal.tsum_toReal_eq ?_).trans ?_
  · intro _; refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
    exact mul_le_one₀ (distr_upper_bound _ _) bot_le (distr_upper_bound _ _)
  · refine tsum_congr fun x ↦ ?_; simp

lemma c_bind_upcl {α β : Type} {s : C α} {k : α → C β} :
    IsUpperSet (distr_bind s.val (Subtype.val ∘ k)) := by
  simp [distr_bind, Set.image]
  intro ν₁ ν₂ hle
  rintro ⟨μ, f, ⟨_, hμ, _, h, _, _⟩, heq⟩; subst heq
  refine ⟨μ, ?_⟩
  by_cases h0 : μ.bind f ⊥ = 0
  · exact ⟨f, ⟨μ, hμ, f, h, rfl⟩, proper_dist_maximal h0 hle⟩
  · -- Δ y is the about of missing probability mass for y, scaled by the amount of unassigned mass
    let Δ (y : β) := (ν₂ y - μ.bind f y) / μ.bind f ⊥
    let g x : Distr β :=
      ⟨ fun y ↦ match y with
        | some y => f x y + f x ⊥ * Δ y
        | none => f x ⊥ * (1 - tsum Δ),
      by
        refine (Equiv.hasSum_iff (Equiv.optionEquivSumPUnit β : Option β ≃ β ⊕ Unit).symm).mp ?_
        refine ENNReal.summable.hasSum_iff.mpr ?_
        rw [tsum_sum ENNReal.summable ENNReal.summable]; simp
        rw [tsum_add ENNReal.summable ENNReal.summable, ENNReal.tsum_mul_left]
        unfold Δ ; sorry
        -- rw [prob_not_bot, add_assoc, ← mul_add]
        -- rw [add_comm (tsum _)]
        -- have hub : ∑' (y : β), (ν₂ ↑y - (μ.bind f) ↑y) / (μ.bind f) ⊥ ≤ 1 := by
        --   rw [tsum_congr fun _ ↦ div_eq_mul_inv _ _, ENNReal.tsum_mul_right,
        --       tsum_sub' _ hle]
        --   · refine (ENNReal.mul_inv_le_iff h0 prob_not_top).mpr ?_
        --     rw [prob_not_bot, prob_not_bot, one_mul]
        --     exact tsub_tsub_tsub_le_tsub.trans tsub_le_self
        --   · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
        --     rw [prob_not_bot]; exact tsub_le_self
        -- have hnt := ne_top_of_le_ne_top ENNReal.one_ne_top hub
        -- rw [ENNReal.sub_add_eq_add_sub hub hnt,
        --     ENNReal.add_sub_cancel_right hnt]; simp
        -- rw [ENNReal.sub_add_eq_add_sub (distr_upper_bound _ _) prob_not_top,
        --     ENNReal.add_sub_cancel_right prob_not_top]
      ⟩
    refine ⟨g, ⟨μ, hμ, g, ?_, rfl⟩, ?_⟩
    · intro x hx; cases x with
      | bot => exact Set.mem_univ _
      | coe x =>
          refine (k x).property.upcl ?_ (h x hx)
          intro y; simp [g, DFunLike.coe]
    · ext y; rw [PMF.bind_apply]; simp [g, Δ, DFunLike.coe]
      have bind_eq z : ∑' (i : WithBot α), μ.val i * (f i).val z = μ.bind f z := rfl
      have bind_eq' z : ∑' (i : WithBot α), μ i * (f i) z = μ.bind f z := rfl
      cases y
      · simp [div_eq_mul_inv, mul_add]
        rw [
          tsum_congr fun _ ↦ (mul_assoc _ _ _).symm.trans (ENNReal.mul_sub ?_),
          tsum_sub',
          ENNReal.tsum_mul_right (a := _ ⁻¹),
          ENNReal.tsum_mul_right, ENNReal.tsum_mul_right
        ]
        simp
        rw [
          bind_eq, mul_comm, mul_assoc, ←distr_coe,
          ENNReal.inv_mul_cancel h0 prob_not_top, mul_one,
          tsum_sub', prob_bot, tsub_tsub,
          add_comm, ENNReal.sub_add_eq_add_sub,
          ← tsum_congr fun _ ↦ distr_coe,
          ← tsum_congr fun _ ↦ distr_coe,
          ENNReal.add_sub_cancel_right,
          ← prob_bot
        ]; rfl
        · rw [prob_not_bot]; simp
        · exact tsum_le_tsum hle ENNReal.summable ENNReal.summable
        · rw [← tsum_congr fun _ ↦ distr_coe, prob_not_bot]; simp
        · rw [← tsum_congr fun _ ↦ distr_coe, prob_not_bot]; simp
        · intro y; exact hle y
        · refine ne_top_of_le_ne_top ENNReal.one_ne_top ?_
          refine LE.le.trans ?_ (distr_upper_bound (μ.bind f) ⊥)
          refine ENNReal.tsum_le_tsum fun x ↦ ?_
          refine mul_le_of_le_one_right bot_le ?_
          rw [ENNReal.tsum_mul_right, tsum_sub' _]
          simp_rw [← distr_coe]
          rw [prob_not_bot, prob_not_bot]
          refine (mul_le_mul (tsub_tsub_tsub_le_tsub) (le_refl _) bot_le bot_le).trans ?_
          rw [
            ENNReal.sub_mul fun _ _ ↦ ENNReal.Finiteness.inv_ne_top h0,
            ENNReal.mul_inv_cancel h0 prob_not_top
          ]; simp
          · intro y; exact hle y
          · simp_rw [← distr_coe]; rw [prob_not_bot]; simp
        · intro y; simp; rw [mul_assoc]
          refine mul_le_mul (le_refl _) ?_ bot_le bot_le
          simp_rw [← distr_coe]
          rw [
            ENNReal.tsum_mul_right,
            tsum_sub' _ hle, prob_not_bot, prob_not_bot
          ]
          refine
            (mul_le_mul (le_refl _)
              (mul_le_mul (tsub_tsub_tsub_le_tsub) (le_refl _) bot_le bot_le)
              bot_le bot_le).trans ?_
          refine mul_le_of_le_one_right bot_le ?_
          rw [ENNReal.sub_mul, ENNReal.mul_inv_cancel h0 prob_not_top]; simp
          · intro _ _; exact ENNReal.Finiteness.inv_ne_top h0
          · simp [prob_not_bot]
        · intro _ _; exact ENNReal.mul_ne_top prob_not_top prob_not_top
      · simp_rw [← distr_coe]
        rw [
          tsum_congr fun _ ↦ mul_add _ _ _,
          tsum_add ENNReal.summable ENNReal.summable,
          tsum_congr fun _ ↦ (mul_assoc _ _ _).symm,
          ENNReal.tsum_mul_right,
          bind_eq', bind_eq', ENNReal.mul_div_cancel h0 prob_not_top,
          add_comm, ENNReal.sub_add_eq_add_sub (hle _) prob_not_top,
          ENNReal.add_sub_cancel_right prob_not_top
        ]

instance : Monad C where
  pure a := ⟨ {PMF.pure ↑a}, c_pure_valid ⟩

  bind {α β : Type} (s : C α) (k : α → C β) :=
    Subtype.mk (distr_bind s.val (Subtype.val ∘ k)) {
      nonempty := c_bind_nonempty
      convex := c_bind_convex
      closed := c_bind_closed
      upcl := c_bind_upcl
    }


namespace C

lemma pure_bind {α β : Type} (x : α) (k : α → C β) : pure x >>= k = k x := by
  simp [Pure.pure, Bind.bind, distr_bind, Set.image, Option.elim]
  refine Subtype.ext ?_; ext d; simp; constructor
  · intro ⟨p, f, ⟨g, hg, hb⟩, h⟩
    rcases Prod.mk.inj_iff.mp hb with ⟨hp, hf⟩; subst hp h hf
    rw [PMF.pure_bind]; exact hg
  · intro hd
    have h : ∀ z, ∃ d', (z = x → d' = d) ∧ d' ∈ k z := by
      intro z; by_cases hz : z = x
      · refine ⟨d, fun _ ↦ rfl, ?_⟩; rw [hz]; exact hd
      · rcases (k z).property.nonempty with ⟨d', hd⟩
        exact ⟨d', fun h ↦ False.elim (hz h), hd⟩
    choose f hf using h
    let g z := match z with
      | none => ⊥
      | some z' => f z'
    refine ⟨PMF.pure x, g, ⟨g, ?_, rfl⟩, ?_⟩
    · simp [g]; exact (hf x).2
    · rw [PMF.pure_bind]; simp [g]; exact (hf x).1 rfl

noncomputable def pmf_with_bot {α β : Type} (f : α → Distr β) (x : WithBot α) : Distr β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y

lemma with_bot_bind {α β γ : Type} {f : α → Distr β} {g : β → Distr γ} :
    (pmf_with_bot fun x => PMF.bind (f x) (pmf_with_bot g)) =
    fun x => PMF.bind (pmf_with_bot f x) (pmf_with_bot g) := by
  unfold pmf_with_bot; ext x y; cases x with
  | bot => simp [Bot.bot]
  | coe z => simp

lemma pmf_bind_congr {α β : Type} {μ : PMF α} {f g : α → PMF β} (h: ∀ x ∈ μ.support, f x = g x) :
    μ.bind f = μ.bind g := by
  ext y; rw [PMF.bind_apply, PMF.bind_apply]; refine tsum_congr ?_
  intro x; by_cases hx : x ∈ μ.support
  · rw [h _ hx]
  · simp at hx; simp [hx]

-- Lemma B.7 from POPL '25
lemma bind_assoc_convex {α β γ : Type} {μ : Distr α} {ν : WithBot α → Distr β} {ξ : WithBot α → WithBot β → Distr γ}
    {g : β → C γ} (h : ∀ x ∈ PMF.support μ, ∀ y ∈ PMF.support (ν x), ξ x y ∈ with_bot g y) :
    ∃ ξ' ∈ (⋃ x ∈ PMF.support μ, PMF.support (ν x)).pi (Subtype.val ∘ with_bot g),
      (PMF.bind μ fun x => PMF.bind (ν x) (ξ x)) = (PMF.bind μ ν).bind ξ' := by
  let p (y : WithBot β) x := μ x * ν x y / PMF.bind μ ν y
  let f y (hy : y ∈ (μ.bind ν).support): Distr α := Subtype.mk (p y) (by {
    unfold p; rw [PMF.bind_apply]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [tsum_congr fun _ ↦ ENNReal.div_eq_inv_mul, ENNReal.tsum_mul_left]
    refine ENNReal.inv_mul_cancel ?_ ?_
    · exact hy
    · intro hc; have h := HasSum.tsum_eq (μ.bind ν).property; simp [PMF.bind] at h
      refine False.elim (ne_top_of_le_ne_top ENNReal.one_ne_top ?_ hc); rw [← h]
      exact ENNReal.le_tsum _
  })
  have hf : ∀ y, ∃ ξ', ∀ hy : y ∈ (μ.bind ν).support, ξ' = f y hy := by
    intro y; by_cases hy : y ∈ (μ.bind ν).support
    · exact ⟨f y hy, fun _ ↦ rfl⟩
    · exact ⟨⊥, fun hc ↦ False.elim (hy hc)⟩
  choose ξ' hξ' using hf
  refine ⟨fun y ↦ PMF.bind (ξ' y) fun x ↦ ξ x y, ?_, ?_⟩
  · intro y; simp; intro x hx hy
    have hy' : y ∈ (μ.bind ν).support := by simp; exact ⟨x, hx, hy⟩
    refine countably_convex' ?_
    intro x'; rw [hξ' y hy']; unfold f; unfold p; intro hp
    refine h x' ?_ y ?_
    · intro hxx; apply hp; simp [DFunLike.coe]; left; left; exact hxx
    · intro hy; apply hp; simp [DFunLike.coe]; left; right; exact hy
  · ext z; simp [PMF.bind_apply]
    rw [← tsum_congr (fun _ ↦ ENNReal.tsum_mul_left)]
    rw [← tsum_congr (fun _ ↦ ENNReal.tsum_mul_left)]
    nth_rewrite 2 [ENNReal.tsum_comm]
    nth_rewrite 2 [← tsum_congr (fun _ ↦ tsum_congr fun _ ↦ mul_assoc (G := ENNReal) _ _ _)]
    rw [← tsum_congr (fun _ ↦ tsum_congr fun _ ↦ ENNReal.tsum_mul_left)]
    rw [tsum_congr fun _ ↦ ENNReal.tsum_comm]
    nth_rewrite 2 [ENNReal.tsum_comm]
    refine tsum_congr fun x ↦ tsum_congr fun y ↦ ?_
    have hξeq : ∑' (a : WithBot α), μ a * (ν a) y * ((ξ' y) x * (ξ x y) z) =
                ∑' (a : WithBot α), μ a * (ν a) y * (p y x * (ξ x y) z) := by
      refine tsum_congr fun x' ↦ ?_; by_cases hx' : μ x' = 0
      · simp [hx']
      · by_cases hy' : (ν x') y = 0
        · simp [hy']
        · refine congrArg₂ _ rfl ?_
          have hy' : y ∈ (μ.bind ν).support := by simp; exact ⟨x', hx', hy'⟩
          rw [hξ' y hy']; unfold f; rfl
    rw [hξeq]; unfold p
    rw [ENNReal.tsum_mul_right, ← mul_assoc, ← mul_assoc]; refine congrArg₂ _ ?_ rfl
    by_cases hy : (ν x) y = 0
    · simp [hy]
    · rw [ENNReal.mul_div_right_comm, ← mul_assoc]; refine congrArg₂ _ ?_ rfl
      refine Eq.symm (ENNReal.mul_div_cancel' ?_ ?_)
      · intro hz; cases mul_eq_zero.mp (ENNReal.tsum_eq_zero.mp hz x)
        · assumption
        · contradiction
      · intro hc; have h := HasSum.tsum_eq (μ.bind ν).property
        refine False.elim (ne_top_of_le_ne_top ENNReal.one_ne_top ?_ hc); rw [← h]
        simp [PMF.bind]; exact ENNReal.le_tsum _

lemma bind_union {α β : Type} (s : C α) (f : α → C β) :
    Subtype.val (bind s f) =
    ⋃ μ ∈ s, PMF.bind μ '' (μ.support.pi (Option.elim · Set.univ (Subtype.val ∘ f))) := by
  simp [Bind.bind, distr_bind]; ext ν; simp; constructor
  · intro ⟨p, g, ⟨hp, hsupp⟩, hν⟩; subst hν
    exact ⟨p, hp, fun x' ↦ g ↑x', hsupp, rfl⟩
  · intro ⟨μ, hμ, g, hsupp, heq⟩; subst heq
    refine ⟨μ, g, ⟨hμ, hsupp⟩, rfl⟩

lemma bind_bind_1 {α β γ : Type}  (s : C α)  (f : α → C β)  (g : β → C γ) :
    Subtype.val (s >>= f >>= g) =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (Subtype.val ∘ with_bot f),
          ∃ ξ ∈ (⋃ x ∈ μ.support, (ν x).support).pi (Subtype.val ∘ with_bot g),
            d = PMF.bind (PMF.bind μ ν) ξ } := by
  simp [Bind.bind, distr_bind, Set.image]; ext d; constructor
  · rintro ⟨ν, g', ⟨_, ⟨μ, f', ⟨_, hμ, f'', hf, _, _⟩, hν⟩, g'', hg, _, _⟩, hd⟩
    subst hd hν; refine ⟨μ , hμ, f', ?_, g', ?_, PMF.bind_bind _ _ _⟩
    · intro x hx; unfold with_bot; cases x
      · simp [Bot.bot]
      · simp; exact hf _ hx
    · intro y x hx hxy; unfold with_bot; cases y with
      | bot => simp [Bot.bot]
      | coe y' => simp; refine hg y' ?_; simp; refine ⟨x, hx, hxy⟩
  · rintro ⟨μ, hμ, ν, hf, ξ, hg, hd⟩; subst hd
    refine ⟨μ.bind ν, ξ, ⟨μ.bind ν, ⟨μ, ν, ⟨μ, hμ, ν, ?_, rfl⟩, rfl⟩, ?_⟩, PMF.bind_bind _ _ _⟩
    · intro x hx; cases x
      · simp [Bot.bot]
      · simp [with_bot] at hf; exact hf _ hx
    · refine ⟨ξ, ?_, rfl⟩; intro y hy; simp at hy; rcases hy with ⟨x, hx, hy⟩
      cases y
      · simp [Bot.bot]
      · simp [with_bot] at hg; exact hg _ x hx hy

lemma bind_bind_2 {α β γ : Type}  (s : C α)  (f : α → C β)  (g : β → C γ) :
    Subtype.val (s >>= fun (x : α) => f x >>= g) =
    { d | ∃ μ  ∈ s,
          ∃ ν ∈ μ.support.pi (Subtype.val ∘ with_bot f),
          ∃ ξ : WithBot α → WithBot β → Distr γ,
            (∀ x ∈ μ.support, ∀ y ∈ (ν x).support, ξ x y ∈ with_bot g y) ∧
            d = PMF.bind μ fun x ↦ PMF.bind (ν x) (ξ x) } := by
  simp [Bind.bind, distr_bind, Set.image]; ext d; constructor
  · rintro ⟨μ, ξ, ⟨_, hμ, _, hξ, _, _⟩, hd⟩; subst hd
    refine ⟨μ, hμ, ?_⟩
    have hν : ∀ x : WithBot α, ∃ ν : Distr β,
        (x ∈ μ.support → ν ∈ with_bot f x) ∧
        ∃ ξ' : WithBot β → Distr γ, x ∈ μ.support →
          ν.bind ξ' = ξ x ∧ ∀ y ∈ ν.support, ξ' y ∈ with_bot g y := by
      intro x; by_cases hx : x ∈ μ.support
      · cases x with
        | bot =>
          refine ⟨⊥, fun _ ↦ Set.mem_univ _, ?_⟩
          have _ (y : WithBot β):= Classical.dec (y = ⊥)
          refine ⟨fun y : WithBot β => if y = ⊥ then ξ ⊥ else ⊥, fun _ ↦ ⟨?_, ?_⟩⟩
          · simp [Bot.bot, PMF.pure_bind]
          · simp [Bot.bot]; exact Set.mem_univ _
        | coe x =>
          have h := hξ _ hx; simp [Option.elim] at h
          rcases h with ⟨ν, ξ', ⟨_, hν, _, h, _, _⟩, heq⟩
          refine ⟨ν, fun _ ↦ hν, ξ', fun _ ↦ ⟨heq, ?_⟩⟩
          intro y hy; cases y
          · exact Set.mem_univ _
          · exact h _ hy
      · refine ⟨⊥, fun hc ↦ False.elim (hx hc), ⟨⊥, fun hc ↦ False.elim (hx hc)⟩⟩
    choose ν hνξ using hν
    have hν x := (hνξ x).1
    have hξ x := (hνξ x).2
    choose ξ' hξ using hξ
    refine ⟨ν, hν, ξ', ?_, ?_⟩
    · intro x hx; exact (hξ x hx).2
    · exact pmf_bind_congr fun x hx ↦ Eq.symm (hξ x hx).1
  · rintro ⟨μ, hμ, ν, hν, ξ, hξ, hd⟩; subst hd
    refine ⟨μ, fun x ↦ (ν x).bind (ξ x), ⟨μ, hμ, fun x ↦ (ν x).bind (ξ x), ?_, rfl⟩, rfl⟩
    intro x hx; simp; cases x with
    | bot => exact Set.mem_univ _
    | coe x =>
      simp [Option.elim]; refine ⟨ν x, ξ x, ⟨ν x, hν _ hx, ξ x, ?_, rfl⟩, rfl⟩
      intro y hy; cases y
      · exact Set.mem_univ ?_
      · exact hξ x hx _ hy

lemma bind_assoc {α β γ : Type} (s : C α)  (f : α → C β)  (g : β → C γ) :
    s >>= f >>= g = s >>= fun (x : α) => f x >>= g := by
  refine Subtype.ext ?_; rw [bind_bind_1, bind_bind_2]; ext d
  refine exists_congr fun μ ↦ and_congr_right fun hμ ↦ ?_
  refine exists_congr fun ν ↦ and_congr_right fun hν ↦ ?_
  constructor
  · intro ⟨ξ, hξ, hd⟩; subst hd; refine ⟨fun _ ↦ ξ, ?_, PMF.bind_bind _ _ _⟩
    intro x hx y hy; simp; simp at hξ; exact hξ y x hx hy
  · intro ⟨ξ, hξ, hd⟩; subst hd
    exact bind_assoc_convex hξ

lemma bind_pure {α : Type} (s : C α) : s >>= pure = s := by
  simp [Bind.bind, Pure.pure, distr_bind, Set.image]
  refine Subtype.ext ?_; simp; ext μ; constructor
  · rintro ⟨ν, f, ⟨_, hν, _, h, _, _⟩, heq⟩; subst heq
    refine s.property.upcl (fun y ↦ ?_) hν
    rw [PMF.bind_apply]
    refine
      LE.le.trans (b := ν.bind pure y)
        (le_of_eq ?_)
        (tsum_le_tsum ?_ ENNReal.summable ENNReal.summable)
    · refine DFunLike.congr_fun ν.bind_pure.symm _
    · intro x; by_cases hx : x ∈ ν.support
      · refine mul_le_mul (le_refl _) ?_ bot_le bot_le
        cases x
        · have hpure : pure (α := WithBot α) = PMF.pure := rfl
          rw [hpure, PMF.pure_apply_of_ne]
          · exact bot_le
          · exact Option.some_ne_none _
        · have hf := h _ hx; simp [Option.elim] at hf; rw [hf]
          exact le_of_eq rfl
      · simp at hx; rw [hx]; simp
  · intro hμ; refine ⟨μ, PMF.pure, ⟨μ, hμ, PMF.pure, ?_, rfl⟩, μ.bind_pure⟩
    intro x hx; cases x
    · exact Set.mem_univ ?_
    · simp [Option.elim]


instance : LawfulMonad C where
  map_const := by intro α β; simp [Functor.mapConst, Functor.map]
  pure_bind := C.pure_bind
  bind_assoc := C.bind_assoc
  id_map := C.bind_pure
  seqLeft_eq := sorry
  seqRight_eq := sorry
  bind_pure_comp := sorry
  pure_seq := sorry
  bind_map := sorry
