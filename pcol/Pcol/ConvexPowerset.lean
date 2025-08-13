import Init.Prelude
import Mathlib

open ENNReal

-- Orders on Probability Distributions

def D (α : Type) : Type := PMF (WithBot α)

instance {α : Type} : FunLike (D α) (WithBot α) ENNReal where
  coe d x := d.1 x
  coe_injective' _ _ h := Subtype.eq h

instance {α : Type} : LE (D α) where
  le d₁ d₂ := ∀ x : α, d₁ x ≤ d₂ x

noncomputable instance {α : Type} : Bot (D α) where
  bot := PMF.pure ⊥
noncomputable instance {α : Type} : OrderBot (D α) where
  bot_le := by {
    intro d x
    unfold Bot.bot instBotD; simp
    rw [PMF.pure_apply_of_ne, ← ENNReal.bot_eq_zero]
    exact bot_le
    simp
  }

instance {α : Type} : Preorder (D α) where
  le_refl d x := le_refl (d x)
  le_trans :=  by {
    intros d₁ d₂ d₃ h₁ h₂ x
    apply le_trans (h₁ x) (h₂ x)
  }

lemma prob_bot {α : Type} (d : D α) : d ⊥ = 1 - ∑' x : α, d x := by {
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

instance {α : Type} : PartialOrder (D α) where
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

def Probability : Set ENNReal := { p : ENNReal | p ≤ 1 }

theorem prob_ne_top {p : ENNReal} (hp : p ≤ 1) : (p : ENNReal) ≠ ⊤ := by
  apply lt_top_iff_ne_top.mp
  refine lt_of_le_of_lt ?_ (ENNReal.one_lt_top)
  assumption

noncomputable def convex_sum' {α : Type} (d₁ d₂ : D α) (p : ENNReal) (hp : p ≤ 1) : D α :=
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


def ConvexSet {α : Type} (S : Set (D α)) : Prop :=
  ∀ d₁ ∈ S, ∀ d₂ ∈ S, ∀ p : ENNReal,
    (h : p ≤ 1) →
    convex_sum' d₁ d₂ p h ∈ S

def UpClosed {α : Type} [LE α] (S : Set α) : Prop :=
  ∀ x ∈ S, ∀ y ≥ x, y ∈ S

def d_to_fun {α : Type} (d : D α) : WithBot α → ENNReal := d.val

instance {α : Type} : TopologicalSpace (D α) :=
  TopologicalSpace.induced d_to_fun Pi.topologicalSpace

-- instance {α : Type} : TopologicalSpace (D α) :=
--   ⨅ (x : WithBot α),
--     TopologicalSpace.induced (fun d : D α => d x) ENNReal.instTopologicalSpace

instance : CompactSpace ENNReal where
  /- TODO -/
  isCompact_univ := by sorry

lemma d_range_prob {α : Type} :
  Set.range d_to_fun ⊆ { f : WithBot α → ENNReal | ∀ x, f x ∈ Probability } := by {
    unfold Set.range
    rintro f ⟨⟨g, hs⟩, hd⟩ x
    simp [Probability, d_to_fun, ← hd] at *
    exact (PMF.coe_le_one ⟨g, hs⟩ x)
  }

lemma d_range_decomp {α : Type} :
  Set.range d_to_fun =
  { f : WithBot α → ENNReal | ∀ x, f x ∈ Probability } ∩
  { f : WithBot α → ENNReal | HasSum f 1 } := by {
    ext f; constructor
    · intro hf; constructor
      · exact (d_range_prob hf)
      · rcases hf with ⟨⟨p, hs⟩, hd⟩
        simp [← hd]
        apply hs
    · rintro ⟨_, hf⟩
      simp at *
      use ⟨f, hf⟩; rfl
  }

instance {α : Type} : CompactSpace (D α) where
  isCompact_univ := by sorry
  /- TODO: fix this proof -/
  --   have hi := (Topology.isInducing_iff (d_to_fun : D α → _)).2 (by rfl)
  --   apply (Topology.IsInducing.isCompact_iff hi).2
  --   simp
  --   rw [d_range_decomp]
  --   apply IsCompact.inter_right
  --   · apply isCompact_pi_infinite
  --     intro _
      -- intro f hnb hle
      -- simp [Filter.principal] at hle
      -- unfold ClusterPt
      -- unfold LE.le at hle
      -- unfold Preorder.toLE at hle
      -- unfold PartialOrder.toPreorder at hle
      -- unfold Filter.instPartialOrder at hle
      -- simp at hle
      -- use 1
      -- constructor
      -- · simp [Probability]
      -- · simp [nhds, Filter.instInf]
      --   apply Filter.neBot_iff.2
      --   unfold Bot.bot
      --   unfold Filter.instBot
      --   simp
      --   intro hc
      --   injection hc with hc
              -- apply Metric.isCompact_iff_isClosed_bounded

  --   · rcases (isClosed_induced_iff.1 (isClosed_univ : IsClosed (Set.univ : Set (D α))))
  --       with ⟨t, hcl, heq⟩
  --     simp at heq

  --   apply (IsCompact.of_isClosed_subset · · d_range_prob)
  --   · apply isCompact_pi_infinite
  --     intro _
  --   · rcases (isClosed_induced_iff.1 (isClosed_univ : IsClosed (Set.univ : Set (D α))))
  --       with ⟨t, hcl, heq⟩
  --     simp at heq
  --     unfold Set.preimage at heq
  --     have h : t = Set.range d_to_fun := by {
  --       ext f; constructor
  --       · intro hf; simp
  --     }

  -- }

def is_valid_C {α : Type} (S : Set (D α)) : Prop :=
  Nonempty S ∧
    ConvexSet S ∧
    IsClosed S ∧
    UpClosed S

def C (α : Type) : Type :=
  { S : Set (D α) // is_valid_C S }

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


noncomputable def pure_d {α : Type} (x : α) : D α := PMF.pure x

lemma up_closed_singleton {α : Type} : ∀ x : α, ∀ d : D α,
  /- TODO -/
  pure_d x ≤ d → d = pure_d x := by {
    intro x d h
    apply PMF.ext
    intro y
    cases y with
    | bot => sorry
    | coe z => sorry
  }

lemma singleton_valid {α : Type} : ∀ x : α, is_valid_C {(PMF.pure x : (D α))} := by {
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
