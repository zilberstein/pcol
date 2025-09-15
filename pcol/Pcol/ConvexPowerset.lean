import Init.Prelude
import Mathlib
import Pcol.Dist

open ENNReal
open PMF

-- Orders on Probability Distributions

instance {α : Type} : LE (Distr α) where
  le d₁ d₂ := ∀ x : α, d₁ x ≤ d₂ x

noncomputable instance {α : Type} : Bot (Distr α) where
  bot := PMF.pure ⊥
noncomputable instance {α : Type} : OrderBot (Distr α) where
  bot_le := by {
    intro d x
    unfold Bot.bot instBotDistr; simp
    rw [PMF.pure_apply_of_ne, ← ENNReal.bot_eq_zero]
    exact bot_le
    simp
  }

instance {α : Type} : Preorder (Distr α) where
  le_refl d x := le_refl (d x)
  le_trans :=  by {
    intros d₁ d₂ d₃ h₁ h₂ x
    apply le_trans (h₁ x) (h₂ x)
  }

instance {α : Type} : PartialOrder (Distr α) where
  le_antisymm := by {
    intro d₁ d₂ h₁ h₂
    apply PMF.ext
    intro x
    have h (y : α) : d₁ y = d₂ y := le_antisymm (h₁ y) (h₂ y)
    cases x
    · rw [prob_bot d₁, prob_bot d₂]
      rw [tsum_congr]
      assumption
    · apply h
  }

theorem prob_ne_top {p : ENNReal} (hp : p ≤ 1) : (p : ENNReal) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  refine lt_of_le_of_lt ?_ (ENNReal.one_lt_top)
  assumption

noncomputable def convex_sum' {α : Type} (d₁ d₂ : Distr α) (p : ENNReal) (hp : p ≤ 1) : Distr α :=
  Subtype.mk (fun x => (p * d₁ x) + ((1-p) * d₂ x))
  (by {
    have h : (1 : ENNReal) = p + (1 - p) := by {
      rw [add_comm, ENNReal.sub_add_eq_add_sub, ENNReal.add_sub_cancel_right]
      all_goals try apply prob_ne_top hp
      assumption
    }
    rw (occs := .pos [2]) [h]
    apply HasSum.add
    · apply ENNReal.summable.hasSum_iff.2
      simp only [ENNReal.tsum_mul_left]
      rw [PMF.tsum_coe, mul_one]
    · apply ENNReal.summable.hasSum_iff.2
      simp only [ENNReal.tsum_mul_left]
      rw [PMF.tsum_coe, mul_one]
  })

def ConvexSet {α : Type} (S : Set (Distr α)) : Prop :=
  ∀ d₁ ∈ S, ∀ d₂ ∈ S, ∀ p : ENNReal,
    (h : p ≤ 1) →
    convex_sum' d₁ d₂ p h ∈ S

-- We may actually need to switch to this definition
noncomputable def ConvexSet' {α : Type} (s : Set (Distr α)) : Prop :=
  ∀ ξ : PMF ↑s, PMF.bind ξ Subtype.val ∈ s

def upClosure {α : Type} [LE α] (S : Set α) : Set α :=
  { y | ∀ x ∈ S , x ≤ y }

lemma dist_le_bot_ge {α : Type} {μ : Distr α} {ν : Distr α} (hle : μ ≤ ν) : ν ⊥ ≤ μ ⊥ := by {
  rw [prob_bot, prob_bot]; simp
  have hs := tsum_le_tsum hle ENNReal.summable ENNReal.summable
  apply le_trans _ (add_le_add_left hs _)
  have hle1 : ∑' (x : α), μ x ≤ 1 := by {
    rcases μ with ⟨d, h⟩; simp [distr_coe] at *; rw [← HasSum.tsum_eq h]
    exact tsum_le_tsum_of_inj WithBot.some WithBot.coe_injective (by simp)
      (fun x => le_refl (d ↑x))
      ENNReal.summable
      ENNReal.summable
  }
  rw [ENNReal.sub_add_eq_add_sub hle1, ENNReal.add_sub_cancel_right]
  all_goals { exact ne_top_of_le_ne_top (b := 1) (by simp) hle1 }
}

lemma proper_dist_maximal {α : Type} {μ ν : Distr α} (hbot : μ ⊥ = 0) :
  μ ≤ ν → μ = ν := by {
    rcases μ with ⟨d₁, hs₁⟩; rcases ν with ⟨d₂, hs₂⟩
    intro hle; ext x; simp [distr_coe]
    have h0 : d₂ ⊥ = 0 := by {
      have h := dist_le_bot_ge hle
      simp [distr_coe] at *
      rw [hbot] at h; simp [hbot, le_bot_iff.1 h]
    }
    match x with
    | ⊥ => simp [distr_coe] at hbot; simp [h0, hbot]
    | WithBot.some y =>
      simp [instLEDistr, distr_coe] at hle
      apply (LE.le.not_lt_iff_eq (hle y)).1; intro hc
      have hs : 1 < tsum d₂ := by {
        rw [← HasSum.tsum_eq hs₁]; apply ENNReal.tsum_lt_tsum
        · simp [HasSum.tsum_eq hs₁]
        · intro z; match z with
          | ⊥ => simp [distr_coe] at hbot; rw [h0, hbot]
          | WithBot.some w => exact hle w
        · exact hc
      }
      apply HasSum.tsum_eq at hs₂; rw [← hs₂] at hs; exact lt_irrefl _ hs
  }

structure is_valid_C {α : Type} (S : Set (Distr α)) : Prop where
  nonempty : S.Nonempty
  convex : Convex ENNReal (Subtype.val '' S)
  closed : IsClosed S
  upcl : IsUpperSet S

def C (α : Type) : Type :=
  { S : Set (Distr α) // is_valid_C S }

lemma hassum_1_convex {α : Type} : Convex ENNReal { d : WithBot α → ENNReal | HasSum d 1} := by
  refine convex_iff_forall_pos.mpr ?_; simp
  intro d hd d' hd' p q hp hq hpq
  have heq (r : ENNReal) (e : WithBot α → ENNReal) : r • e = fun x => r • e x := rfl
  have hr (r : ENNReal) : r = r • 1 := by simp
  rw [← hpq, heq p d, heq q d']; refine HasSum.add ?_ ?_
  · nth_rewrite 2 [hr p]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [ENNReal.tsum_const_smul p, HasSum.tsum_eq hd]
  · nth_rewrite 2 [hr q]; refine (Summable.hasSum_iff ENNReal.summable).mpr ?_
    rw [ENNReal.tsum_const_smul q, HasSum.tsum_eq hd']

instance {α : Type} : Bot (C α) where
  bot := Subtype.mk Set.univ (by constructor <;> simp [isClosed_univ, IsUpperSet, hassum_1_convex])

def with_bot {α β : Type} (f : α → C β) (x : WithBot α) : C β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y

instance {α : Type} : Membership (Distr α) (C α) where
  mem s d := d ∈ s.val


def SmythOrd {α : Type} [LE α] (S T : Set α) :=
  ∀ y ∈ T, ∃ x ∈ S, x ≤ y

instance {α : Type} : LE (C α) where
  le S T := SmythOrd S.val T.val

lemma le_iff_supset {α : Type} {S T : C α} :
  S ≤ T ↔ T.val ⊆ S.val := by {
    constructor
    · intro h d hd
      rcases (h d hd) with ⟨ d', hd', hle ⟩
      rcases S with ⟨S, ⟨_, _, _, hu⟩⟩
      exact hu hle hd'
    · intro h d hd
      exists d; constructor
      · exact (Set.mem_of_subset_of_mem h hd)
      · simp
  }

instance {α : Type} : OrderBot (C α) where
  bot_le s := by apply le_iff_supset.2; simp [Bot.bot]

instance {α : Type} : Preorder (C α) where
  le_refl S := le_iff_supset.2 (le_refl S.val)
  le_trans S T U h₁ h₂ := by {
    apply le_iff_supset.2
    have h₁' := le_iff_supset.1 h₁
    have h₂' := le_iff_supset.1 h₂
    exact (le_trans h₂' h₁')
  }

instance {α : Type} : PartialOrder (C α) where
  le_antisymm _ _ h₁ h₂ :=
    Subtype.eq <|
      (le_antisymm (le_iff_supset.1 h₂) (le_iff_supset.1 h₁) )

instance {α : Type} : Bot (C α) where
  bot := Subtype.mk Set.univ <| by
    constructor
    · simp
    · simp [hassum_1_convex]
    · apply isClosed_univ
    · intro _ _ _ _ ; simp

instance {α : Type} : OrderBot (C α) where
  bot_le S := by {
    apply le_iff_supset.2
    apply Set.subset_univ
  }

noncomputable instance {α : Type} : SupSet (C α) where
  sSup s := by {
    let t := Set.sInter (Subtype.val '' s)
    by_cases h : is_valid_C t
    · exact ⟨t, h⟩
    · exact ⊥
  }

-- For any directed set, the supremum is equal to set intersection
lemma sSup_of_directed {α : Type} {s : Set (C α)} (hd : DirectedOn (· ≤ ·) s) :
  (sSup s).val = (Subtype.val '' s).sInter := by {
    have hv (h : s.Nonempty) : is_valid_C (Subtype.val '' s).sInter := by {
      have hne' := Set.nonempty_coe_sort.2 (Set.Nonempty.image Subtype.val h)
      refine ⟨?_,?_,?_,?_⟩
      · apply IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed (hS := hne')
        · rintro x ⟨x', hxs, hx⟩ y ⟨y', hys, hy⟩
          rcases hd x' hxs y' hys with ⟨t, ht, htx, hty⟩; use t.val
          simp ; refine ⟨⟨t.2, ht⟩, ?_, ?_⟩
          · rw [← hx]; exact le_iff_supset.1 htx
          · rw [← hy]; exact le_iff_supset.1 hty
        · rintro _ ⟨⟨_, hne, _⟩, _, hvu⟩; rw [← hvu]; exact hne
        · rintro _ ⟨⟨_, _, _, hcl, _⟩, _, hvu⟩; rw [← hvu]; exact IsClosed.isCompact hcl
        · rintro _ ⟨⟨_, _, _, hcl, _⟩, _, hvu⟩; rw [← hvu]; exact hcl
      · sorry -- This case is very hard
      · apply isClosed_sInter; rintro t ⟨⟨t', ⟨_, _, hcl, _⟩⟩, _, htt'⟩
        rw [← htt']; exact hcl
      · rintro μ ν hle hμ t ⟨⟨c, hv⟩, hcs, hct⟩
        have hμc : μ ∈ c := by apply hμ; exact ⟨⟨c, hv⟩, hcs, rfl⟩
        simp [← hct]; rcases hv with ⟨_,_,_,hu⟩; exact hu hle hμc
    }
    simp [sSup]; by_cases hne : s.Nonempty
    · rw [dite_cond_eq_true]; exact propext ⟨fun _ => trivial, fun _ => hv hne⟩
    · simp [Set.not_nonempty_iff_eq_empty.1 hne, Bot.bot]
      by_cases hv : is_valid_C (⋂₀ (Subtype.val '' s))
      · rw [dite_cond_eq_true]; exact propext ⟨fun _ => trivial, fun _ => hv⟩
      · rw [dite_cond_eq_false]; exact propext ⟨hv, False.elim⟩
  }

noncomputable instance {α : Type} : CompletePartialOrder (C α) where
  lubOfDirected d hd := by {
    constructor
    · intro c hc; apply le_iff_supset.2
      rw [sSup_of_directed hd]; intro μ hμ; apply hμ; simp; exact ⟨c.2, hc⟩
    · intro c hc; apply le_iff_supset.2; rw [sSup_of_directed hd]
      rintro μ hμ t ⟨t', hth, htt'⟩; rw [← htt']; exact le_iff_supset.1 (hc hth) hμ
  }
