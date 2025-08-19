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

def UpClosed {α : Type} [LE α] (S : Set α) : Prop :=
  ∀ x ∈ S, ∀ y ≥ x, y ∈ S

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

def is_valid_C {α : Type} (S : Set (Distr α)) : Prop :=
  Nonempty S ∧
    ConvexSet S ∧
    IsClosed S ∧
    UpClosed S

def C (α : Type) : Type :=
  { S : Set (Distr α) // is_valid_C S }

instance {α : Type} : Bot (C α) where
  bot := Subtype.mk Set.univ (by unfold is_valid_C; simp [isClosed_univ, ConvexSet, UpClosed])

def with_bot {α β : Type} (f : α → C β) (x : WithBot α) : C β :=
  match x with
  | ⊥ => ⊥
  | WithBot.some y => f y

instance : Monad C where
  pure a := ⟨ {PMF.pure ↑a}, by {
    refine ⟨by simp,?_ , ?_, ?_⟩
    · unfold ConvexSet; simp; intros p hp
      unfold convex_sum'
      ext x
      classical
      match em (x = a) with
      | Or.inl heq =>
        nth_rewrite 1 [distr_coe]; simp
        rw [heq, pure_apply_self]
        simp
        have ht : p ≠ ⊤ := ne_top_of_le_ne_top (by simp) hp
        rw [add_comm, ENNReal.sub_add_eq_add_sub hp ht, ENNReal.add_sub_cancel_right ht]
      | Or.inr hne =>
        rw [PMF.pure_apply_of_ne]
        · nth_rewrite 1 [distr_coe]; simp; refine ⟨?_ ,?_⟩
          all_goals { right; exact PMF.pure_apply_of_ne _ _ hne }
        · refine Ne.intro ?_
          intros hc
          contradiction
    · exact isClosed_singleton
    · unfold UpClosed; simp; intro μ hμ
      symm; apply proper_dist_maximal _ hμ
      rw [PMF.pure_apply_of_ne]; simp
  } ⟩

  bind {α β : Type} (s : C α) (k : α → C β) :=
    Subtype.mk (distr_bind s.val (Subtype.val ∘ k)) (by {
    rcases s with ⟨s, ⟨hne, hu, hcv, hcm⟩⟩; unfold distr_bind
    refine ⟨?_, ?_, ?_, ?_⟩
    · rcases hne with ⟨μ, hμ⟩
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
      rcases hf with ⟨f, hf⟩; use (PMF.bind μ f); simp; use μ
      refine ⟨hμ, ?_⟩; use f; refine ⟨?_, rfl⟩
      · intro x hx; unfold g at hf; exact Set.mem_pi.1 hf x hx
    · sorry
    · apply bind_closed
      intro x; rcases hk : k x with @⟨t, ⟨_, _, hcl, _⟩⟩
      simp [hk, hcl]
    · sorry
  })

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
      apply (hu d' hd' d hle)
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
    · constructor
      · intro _ _ _ _ _ _; simp
      · constructor
        · apply isClosed_univ
        · intro _ _ _ _ ; simp

instance {α : Type} : OrderBot (C α) where
  bot_le S := by {
    apply le_iff_supset.2
    apply Set.subset_univ
  }

def DirSet (α : Type) [LE α]:=
  { s : Set α // Nonempty s ∧ DirectedOn (· ≤ ·) s }

class DCPO (α : Type) extends PartialOrder α where
  dSup : DirSet α → α
  dSupIsLub : ∀ d, IsLUB d.val (dSup d)

lemma convex_set_compact {α : Type} : ∀ s : C α, IsCompact s.val := by {
  intro s
  apply IsCompact.of_isClosed_subset isCompact_univ
  · rcases s with ⟨s, _, _, hc, _⟩
    apply hc
  · simp
}

lemma nonempty_subtype_map {α : Type} {P : α → Prop}: ∀ s : Set {x // P x},
  Nonempty s ↔ Nonempty (Subtype.val <$> s) := by {
    intro s
    constructor
    · rintro ⟨⟨x, p⟩, hx⟩
      use x; simp [p]; assumption
    · rintro ⟨x, ⟨x', ⟨hx', p⟩⟩⟩
      use x'
  }

-- lemma nonempty_inter_subtype {α : Type} {p : Set α → Prop} :
--   ∀ s : Set { t // p t },
--     Nonempty (Set.sInter s) →
--     Nonempty (Set.sInter (Subtype.val <$> s)) := by {
--       intro
-- }

instance {α : Type} : DCPO (C α) where
  dSup d := by sorry
  /- TODO: fix this proof -/
--Subtype.mk (Set.sInter (Functor.map Subtype.val d.val)) <| by
--    constructor
--    · rcases d with ⟨s, hne, hdir⟩
--      let s' := Subtype.val <$> s
--      have hS : Nonempty s' := by {
--        rcases hne with ⟨t, ht⟩
--        use t.val; simp [s']
--        exact ⟨t.2, ht⟩
--      }
--      have hdir' : DirectedOn (· ⊇ ·) s' := by {
--        rintro x ⟨x', hx', hx⟩ y ⟨y', hy', hy⟩
--        rcases (hdir x' hx' y' hy') with ⟨z, ⟨hz, hxz, hyz⟩⟩
--        use z.val; constructor
--        · simp [s']; exact ⟨z.2, hz⟩
--        · simp [Superset, ← hx, ← hy]
--          exact ⟨ le_iff_supset.1 hxz, le_iff_supset.1 hyz ⟩
--      }
--      have hne' : ∀ t ∈ s', t.Nonempty := by {
--        rintro t ⟨⟨t', ⟨u,hnet⟩, _⟩, _, ht⟩
--        simp [← ht]
--        use u
--      }
--      have hSc : ∀ t ∈ s', IsCompact t := by {
--        rintro t ⟨_, _, ht⟩
--        rw [← ht]
--        apply convex_set_compact
--      }
--      have hScl : ∀ t ∈ s', IsClosed t := by {
--        rintro t ⟨⟨t', _, _, hcl, _⟩, _, ht⟩
--        rw [← ht]
--        assumption
--      }
--      have h :=
--        IsCompact.nonempty_sInter_of_directed_nonempty_isCompact_isClosed
--          hdir' hne' hSc hScl
--      rcases h with ⟨d, _⟩
--      use d
--    · constructor
--      · intro d hd d' hd' p hp
--        sorry
--      · constructor
--        · apply isClosed_sInter
--          intro T ht
--          rcases ht with ⟨ ⟨U, ⟨_, _, hc, _⟩⟩, _, hxt ⟩
--          rw [← hxt]
--          assumption
--        · intro d hd d' hle T ht
--          have ht' := ht
--          rcases ht' with ⟨⟨U, ⟨_, _, _, hup⟩⟩, hu, ht1⟩
--          have hut : U = T := by rw [← ht1]
--          rw [hut] at hup
--          exact (hup d (Set.mem_sInter.1 hd _ ht) d' hle)
  dSupIsLub := by sorry
-- by {
--    intro s
--    constructor
--    · unfold upperBounds; intro t ht
--      apply le_iff_supset.2
--      intro u hu
--      apply (Set.mem_sInter.2 hu)
--      simp; constructor
--      · rcases t with ⟨t', hv⟩
--        exact hv
--      · exact ht
--    · intro T ht
--      apply le_iff_supset.2
--      intro d hd
--      unfold upperBounds at ht; simp at ht
--      have h : ∀ U ∈ Subtype.val <$> S, d ∈ U := by {
--        intro U hu
--        rcases hu with ⟨ V, hv, hvu ⟩
--        rw [← hvu] at *
--        exact (le_iff_supset.1 (ht hv) hd)
--      }
--      intro U hu
--      exact (h U hu)
-- }


noncomputable def pure_d {α : Type} (x : α) : Distr α := PMF.pure x

lemma up_closed_singleton {α : Type} : ∀ x : α, ∀ d : Distr α,
  /- TODO -/
  pure_d x ≤ d → d = pure_d x := by {
    intro x d h
    apply PMF.ext
    intro y
    cases y with
    | bot => sorry
    | coe z => sorry
  }

lemma singleton_valid {α : Type} : ∀ x : α, is_valid_C {(PMF.pure x : (Distr α))} := by {
  /- TODO -/
  intro x; unfold is_valid_C; constructor
  · simp
  · constructor
    · intro d₁ h₁ d₂ h₂ p h
      simp at *
      rw [h₁, h₂]
      apply PMF.ext
      intro y; unfold convex_sum'; simp
      sorry
    · constructor
      · sorry
      · intro d hd d' hd'
        simp at *
        apply up_closed_singleton
        unfold pure_d
        rw [← hd]
        assumption
}

instance : Pure C where
  pure x := Subtype.mk { pure_d x } (singleton_valid x)

-- instance : Functor C where
--   map f S := Subtype.mk
--     (
--       Functor.map (Subtype.mk (Functor.map (some ∘ f ∘ Subtype.val)) _) S.val
--     )
--     _

def IsLfp {α : Type} [LE α] (f : α → α) (x : α) : Prop :=
  f x = x ∧ ∀ y : α, f y = y → x ≤ y

def iter {α : Type} (f : α → α) (n : ℕ) : α → α :=
  match n with
  | 0 => id
  | Nat.succ k => f ∘ iter f k

lemma iter_app {α : Type} :
  ∀ (f : α → α), ∀ n, f ∘ (iter f n) = iter f (Nat.succ n) := by {
    intro f n
    simp [iter]
  }

lemma iter_succ_mono {α : Type} (f : α → α) [Preorder α] [OrderBot α] :
  Monotone f → ∀ n, iter f n ⊥ ≤ iter f n.succ ⊥ := by {
  intro hm n
  induction n with
  | zero => simp [iter]
  | succ n' ih =>
    rw [← iter_app]; rw [← iter_app]
    simp
    apply hm ih
  }

lemma iter_mono {α : Type} (f : α → α) [Preorder α] [OrderBot α] :
  Monotone f → Monotone (iter f · ⊥) := by {
  intro hm n m hle; simp
  rw [← Nat.add_sub_of_le hle] at *
  induction (m - n) with
  | zero => simp
  | succ n' ih =>
      apply le_trans ih
      have hs : n + (n' + 1) = Nat.succ (n + n') := by linarith
      rw [hs]
      apply iter_succ_mono f hm
}

lemma chain_dir {α : Type} [Preorder α] [OrderBot α] :
  ∀ (f : α → α),
    Monotone f →
    let s := { iter f n ⊥ | n : ℕ }
    s.Nonempty /\ DirectedOn (· ≤ ·) s := by {
      intro f hm s
      constructor
      · use ⊥; simp [s]
        use 0; simp [iter]
      · intro x hx y hy
        rcases hx with ⟨n₁, hx⟩
        rcases hy with ⟨n₂, hy⟩
        use (iter f (max n₁ n₂) ⊥)
        constructor
        · simp [s]
        · constructor
          · simp [← hx]
            exact iter_mono f hm (le_max_left n₁ n₂)
          · simp [← hy]
            exact iter_mono f hm (le_max_right n₁ n₂)
    }

theorem KleeneFixpoint {α : Type} [CompletePartialOrder α] [OrderBot α] (f : α → α):
  /- TODO -/
  Monotone f →
  ScottContinuous f →
  IsLfp f (⨆ (n : ℕ), iter f n ⊥) := by {
    intro hm hc
    sorry
  -- constructor
  --  · rcases (chain_dir f hm) with ⟨hne, hdir⟩
  --    specialize hc hne hdir
  --    symm
  }
