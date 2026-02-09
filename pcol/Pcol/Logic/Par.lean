import Mathlib.Data.Finset.Lattice.Basic

import Pcol.ConvexPowerset
import Pcol.ConvexPowerset.Monad

import Pcol.Logic.ConvexPowerset
import Pcol.Logic.Lang
import Pcol.Logic.Mem
import Pcol.Logic.MinProb
import Pcol.Semantics.Linearization
import Pcol.Semantics.Lpo.Operations.Par

open Classical

noncomputable def marginalize {α β : Type} (μ : Distr (α × β)) : Distr α :=
  ⟨ fun
    | .none => μ .none
    | .some a => ∑' b : β, μ (a, b)
  , sorry ⟩

noncomputable def mar {α β : Type} (S : C (α × β)) : C α :=
  ⟨ { marginalize μ | μ ∈ S } , sorry ⟩

lemma minProb_mar {α β : Type}
  (S : C (α × β)) (A : Set α) (B : Set β) :
  B = Set.univ →
  minProb (mar S) A = minProb S (Set.prod A B) := by
  sorry

lemma nondet_singleton {ι X : Type} {A : Set ι} {f : ι → C X} :
    ∀ x : ι, A = { x } →
    Lin.nondet f = f x := sorry

lemma minProb_nondet {u : Finset Var} {ι : Type} (f : ι → C Mem) (A : Set Mem) :
    minProb (Lin.nondet f) A =
    ⨅ x : ι, minProb (f x) A := sorry

-- Parallel composition of α and β by upcasting
noncomputable def par_comp {act test : Type}
    (root : Node)
    (α : Lpofin (Label act test))
    (β : Lpofin (Label act test))
    : Lpofin (Label act test) :=
  Lpo.par_fin Label.lab_fork root α β

lemma par_comp_lab_root {act test : Type}
    (α : Lpofin (Label act test))
    (β : Lpofin (Label act test))
    (root : Node)
  : (par_comp root α β).lab root = Label.lab_fork := by
    simp only [Lpofin.lab, Lpo.lab, par_comp, Lpo.par_fin, Lpo.par_base]
    simp

lemma par_comp_comm {act test : Type}
    (α : Lpofin (Label act test))
    (β : Lpofin (Label act test))
    (root : Node) :
    par_comp root α β = par_comp root β α := sorry

-- The set of next nodes in a parallel composition is either
-- 1) Only the root
-- 2) The union of (nonempty) next node sets from α and β
-- 3) The next nodes of α (if β is done executing)
-- 4) The next nodes of β (if β is done executing)
lemma next_par {act test : Type}
    (α : Lpofin (Label act test))
    (β : Lpofin (Label act test))
    (root : Node)
    (s : Finset Node) :
    Lin.next (par_comp root α β) s = {root} ∨
    (Lin.next (par_comp root α β) s = Lin.next α (s ∩ α.nodes_finset) ∪ Lin.next β (s ∩ β.nodes_finset) ∧
      s ∩ α.nodes_finset ≠ ∅ ∧ s ∩ β.nodes_finset ≠ ∅) ∨
    (Lin.next (par_comp root α β) s = Lin.next α (s ∩ α.nodes_finset) ∧
      s ∩ α.nodes_finset ≠ ∅) ∨
    (Lin.next (par_comp root α β) s = Lin.next β (s ∩ β.nodes_finset) ∧
      s ∩ β.nodes_finset ≠ ∅)
    := sorry

variable
  {act test : Type}
  [Sem act Mem (C Mem)]
  [Sem test Mem Bool]
  (root : Node)
--   (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes)
--  {inv : Finset (Mem v)}
--  (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂)
--  (hdn : Disjoint α.nodes β.nodes)
--  (A : Set (Mem (u₁ \ v))) (B : Set (Mem (u₂ \ v)))

-- Shorthand for the independence property
--
-- Note that this is not actually indepedence, as it is an inequality rather than an equality. The equality
-- holds as long as α and β do not rely on each other's private variables, which would manifest as
-- nontermination (⊥), whereas it would be valid in α || β.
--
-- It is easier to prove the inequality than to string through extra assumptions. The inequality will become
-- and equality later, once we show that the minimum probabilities of all events add to 1, so that no
-- event can have probability strictly greater than its lower bound.
def is_indep
  (ℐ 𝒢 : Mem.Inv)
  (α β : Lpofin (Label act test))
  (s : Finset Node) (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Set Mem) (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv)
  /-(s : Finset Node) (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (_ : τ ∈ inv) (_ : τ₁ ∈ inv) (_ : τ₂ ∈ inv)
      (_ : α.has_inv inv) (_ : β.has_inv inv)-/
  : Prop :=
  -- TODO:
  --  * shared global rely?
  --  * establish restrictions / conditions on pₖ ?
  --  * use fun _ => 1 instead of ω ?
  minProb (mar (Lin.lin_rec ℐ ℐ 𝒢 (par_comp root α β) s ⟨σ₁ ⊎ σ₂ ⊎ τ, ω, n₁ + n₂, curr_inv⟩))
          (A ** B ** ℐ.2)
  ≥ minProb (mar (Lin.lin_rec ℐ ℐ 𝒢 α (s ∩ α.nodes_finset) ⟨σ₁ ⊎ τ₁, ω, n₁, curr_inv⟩)) (A ** ℐ.2) *
    minProb (mar (Lin.lin_rec 𝒢 ℐ ℐ β (s ∩ β.nodes_finset) ⟨σ₂ ⊎ τ₂, pₖ, n₂, curr_inv⟩)) (B ** ℐ.2)

-- The inductive step broken into its own lemma, since it needs to be invoked multiple times
lemma par_comp_inductive_step_left
  {ℐ 𝒢 : Mem.Inv} {α β : Lpofin (Label act test)}
  {x : Node} (s : Finset Node)
  (hx : x ∈ Lin.next α (s ∩ α.nodes_finset))
  (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Set Mem)
  -- TODO : well-formedness conditions on memories / sets of memories
  (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv)
  (hτ : τ ∈ ℐ) (hτ₁ : τ₁ ∈ ℐ) (hτ₂ : τ₂ ∈ ℐ)
  (hind : ∀ t ⊆ s,
    ∀ (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Set Mem) (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv)
      (hτ : τ ∈ ℐ) (hτ₁ : τ₁ ∈ ℐ) (hτ₂ : τ₂ ∈ ℐ),
      is_indep root ℐ 𝒢 α β t σ₁ σ₂ τ τ₁ τ₂ A B ω pₖ n₁ n₂ curr_inv)
  :
    minProb (mar (Lin.lin_node ℐ ℐ 𝒢 (par_comp root α β) s x ⟨σ₁ ⊎ σ₂ ⊎ τ, ω, n₁ + n₂, curr_inv⟩)) (A ** B ** ℐ.2)
  ≥ minProb (mar (Lin.lin_node ℐ ℐ 𝒢 α (s ∩ α.nodes_finset) x ⟨σ₁ ⊎ τ₁, ω, n₁, curr_inv⟩)) (A ** ℐ.2) *
    minProb (mar (Lin.lin_rec 𝒢 ℐ ℐ β (s ∩ β.nodes_finset) ⟨σ₂ ⊎ τ₂, pₖ, n₂, curr_inv⟩)) (B ** ℐ.2)
  := by
  unfold Lin.lin_node
  have hlab_eq : (par_comp root α β).lab x = α.lab x := sorry
  rw [hlab_eq]
  cases hlab : α.lab x with
  -- Case : α.lab x = ⊥
  | lab_bot =>
    simp [minProb_mar, minProb_bot]
  -- Case : α.lab x = Fork
  | lab_fork =>
    simp
    apply hind ; all_goals try assumption
    simp
  -- Case : α.lab x = act
  | lab_act a =>
    rw [union_comm, ←union_assoc, union_comm, union_comm τ σ₁]
    simp only [minProb_mar, Lin.State.curr_inv, Lin.State.state]
    refine
      le_trans
        ?_
        (minProb_mono (LawfulLin.bind_mono_left (upcast_mono a curr_inv (σ₁ ⊎ τ) σ₂)))
    rw [bind_assoc, minProb_bind, minProb_bind]
    refine le_of_eq_of_le iInf_C_mul_minProb ?_
    have real_hτ : τ ∈ curr_inv := by sorry
    have real_hτ₁ : τ₁ ∈ curr_inv := by sorry
    rw [inv_sem_eq a σ₁ real_hτ real_hτ₁]
    apply iInf₂_mono
    intros μ hμ
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun ⟨σ, hσ⟩ => ?_
    refine le_of_eq_of_le
      (mul_assoc _ _ _)
      (mul_le_mul (le_refl _) ?_ bot_le bot_le)
    rw [←minProb_mar, ←minProb_mar, ←minProb_mar, pure_bind] ; all_goals try simp
    obtain ⟨σ', τ', heq, hτ'⟩ : ∃ σ', ∃ τ', σ = σ' ⊎ τ' ∧ τ' ∈ ℐ := by sorry
    simp only [heq]
    rw [←union_assoc, union_comm τ' σ₂]
    apply hind ; all_goals try assumption
    apply Set.Subset.refl
  -- Case : α.lab x = test
  | lab_test b =>
    rw [union_comm, ←union_assoc, union_comm, union_comm τ σ₁]
    simp only [minProb_mar, Lin.State.curr_inv, Lin.State.state]
    refine
      le_trans
        ?_
        (minProb_mono (LawfulLin.bind_mono_left (upcast_mono_test b curr_inv (σ₁ ⊎ τ) σ₂)))
    rw [minProb_bind, minProb_bind]
    refine le_of_eq_of_le iInf_C_mul_minProb ?_
    have real_hτ : τ ∈ curr_inv := by sorry
    have real_hτ₁ : τ₁ ∈ curr_inv := by sorry
    rw [inv_sem_eq_test b σ₁ real_hτ real_hτ₁]
    apply iInf₂_mono
    intros μ hμ
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun ⟨r, hr⟩ => ?_
    refine le_of_eq_of_le
      (mul_assoc _ _ _)
      (mul_le_mul (le_refl _) ?_ bot_le bot_le)
    rw [←minProb_mar, ←minProb_mar, ←minProb_mar] ; all_goals try simp
    have heq₁ :
        Lin.filter_by_outcome α (s ∩ α.nodes_finset) x r =
          (Lin.filter_by_outcome α s x r) ∩ α.nodes_finset := by
        simp [Lin.filter_by_outcome, Finset.filter_inter]
    have heq₂ :
      s ∩ β.nodes_finset = (Lin.filter_by_outcome α s x r) ∩ β.nodes_finset := by
          sorry
    have heq₃ :
        Lin.filter_by_outcome (par_comp root α β) s x r = Lin.filter_by_outcome α s x r :=
        sorry
    rw [heq₁, heq₂, heq₃]
    rw [←union_assoc, union_comm τ σ₂]
    apply hind ; all_goals try assumption
    simp [Lin.filter_by_outcome]

-- Version of the previous lemma but swapped so that β is taking a step instead of α
lemma par_comp_inductive_step_right
  {ℐ 𝒢 : Mem.Inv} {α β : Lpofin (Label act test)}
  {x : Node} (s : Finset Node)
  (hx : x ∈ Lin.next α (s ∩ α.nodes_finset))
  (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Set Mem)
  -- TODO : well-formedness conditions on memories / sets of memories
  (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv)
  (hτ : τ ∈ ℐ) (hτ₁ : τ₁ ∈ ℐ) (hτ₂ : τ₂ ∈ ℐ)
  (hind : ∀ t ⊆ s,
    ∀ (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Set Mem) (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv)
      (hτ : τ ∈ ℐ) (hτ₁ : τ₁ ∈ ℐ) (hτ₂ : τ₂ ∈ ℐ),
      is_indep root ℐ 𝒢 α β t σ₁ σ₂ τ τ₁ τ₂ A B ω pₖ n₁ n₂ curr_inv)
  :
    minProb (mar (Lin.lin_node ℐ ℐ 𝒢 (par_comp root α β) s x ⟨σ₁ ⊎ σ₂ ⊎ τ, ω, n₁ + n₂, curr_inv⟩)) (A ** B ** ℐ.2)
  ≥ minProb (mar (Lin.lin_rec ℐ ℐ 𝒢 α (s ∩ α.nodes_finset) ⟨σ₁ ⊎ τ₁, ω, n₁, curr_inv⟩)) (A ** ℐ.2) *
    minProb (mar (Lin.lin_node 𝒢 ℐ ℐ β (s ∩ β.nodes_finset) x ⟨σ₂ ⊎ τ₂, pₖ, n₂, curr_inv⟩)) (B ** ℐ.2)
  := by
  sorry

-- Lemma C.3 from POPL'26
theorem par_comp_fin
  {ℐ 𝒢 : Mem.Inv} {α β : Lpofin (Label act test)} {U₁ U₂ V : Finset Var}
  (σ₁ σ₂ τ τ₁ τ₂ : Mem) (A B : Mems)
  (ω pₖ : ℕ → ENNReal) (n₁ n₂ : ℕ) (curr_inv : Mem.Inv) :
    Disjoint U₁ U₂ → Disjoint U₁ V → Disjoint U₂ V →
    σ₁.dom = U₁ → σ₂.dom = U₂ →
    A.1 = U₁ → B.1 = U₂ → ℐ.1 = V → 𝒢.1 ⊆ V →
    σ₁.wf? → σ₂.wf? → A.wf? → B.wf? →
    τ ∈ ℐ → τ₁ ∈ ℐ → τ₂ ∈ ℐ →
    minProb
      (mar (Lin.lin ℐ ℐ 𝒢 pₖ (par_comp root α β) ⟨σ₁ ⊎ σ₂ ⊎ τ, n₁ + n₂⟩))
      (A.2 ** B.2 ** ℐ.2)
  ≥ minProb (mar (Lin.lin ℐ ℐ 𝒢 ω α ⟨σ₁ ⊎ τ₁, n₁⟩)) (A.2 ** ℐ.2) *
    minProb (mar (Lin.lin 𝒢 ℐ ℐ ω β ⟨σ₂ ⊎ τ₂, n₂⟩)) (B.2 ** ℐ.2) := by
  unfold Lin.lin
  generalize hs : (par_comp root α β).nodes_finset = s
  have h₁ : α.nodes_finset = s ∩ α.nodes_finset := sorry; rw [h₁]
  have h₂ : β.nodes_finset = s ∩ β.nodes_finset := sorry; rw [h₂]
  clear h₁ h₂ hs; revert σ₁ σ₂ τ τ₁ τ₂
  induction s using Finset.strongInduction with
  | H s hind =>
    intro σ₁ σ₂ τ τ₁ τ₂
    intro hdisj₁ hdisj₂ hdisj₂
    intro hσ₁_dom hσ₂_dom hA_dom hB_dom hℐ_dom h𝒢_dom
    intro hσ₁ hσ₂ hA hB
    intro hτ hτ₁ hτ₂
    by_cases hemp : s = ∅
    -- Base Case: No more nodes to schedule
    · unfold Lin.lin_rec
      simp only [hemp, ↓reduceIte, Finset.empty_inter]
      simp only [Lin.State.state, check]
      have heq₁ : (σ₁ ⊎ σ₂ ⊎ τ).proj 𝒢.1 = τ.proj 𝒢.1 := sorry
      have heq₂ : (σ₁ ⊎ τ₁).proj 𝒢.1 = τ₁.proj 𝒢.1 := sorry
      have heq₃ : (σ₂ ⊎ τ₂).proj ℐ.1 = τ₂.proj ℐ.1 := sorry
      rw [heq₁, heq₂, heq₃]
      by_cases h : τ.proj 𝒢.1 ∈ 𝒢.2 <;> simp only [Mem.proj] at *
      · rw [if_pos h, if_pos, if_pos]
        -- TODO: do τ₁ and τ₂ actually belong to  based on τ ∈ 𝒢...?
        · simp only [pure_bind, minProb_mar, minProb_pure, Lin.State.step]
          by_cases hinσ₁ : σ₁ ∈ A <;> by_cases hinσ₂ : σ₂ ∈ B
          · sorry
          · sorry
          · sorry
          · sorry
        · sorry
        · sorry
      · rw [if_neg h, if_neg, if_neg]
        simp only [C.bot_bind, minProb_mar, minProb_bot]
        · simp
        · sorry
        · sorry
--      , minProb_pure, Mem.union_mem]
--      by_cases h₁ : σ₁ ∈ A <;> by_cases h₂ : σ₂ ∈ B <;>
--        simp only [h₁, h₂, Finset.mem_coe.mpr hτ, Finset.mem_coe.mpr hτ₁, Finset.mem_coe.mpr hτ₂,
--          and_true, and_false, ↓reduceIte, and_self, mul_zero, mul_one, le_refl]
    -- Inductive Case
    · nth_rw 1 [Lin.lin_rec]; simp only [hemp, ↓reduceIte]
      rcases next_par α β root s with hnext | ⟨hnext, hne, hne'⟩ | ⟨hnext, hne⟩ | ⟨hnext, hne⟩
      · simp only [Lin.State.prob]
        rw [nondet_singleton ⟨root, by simp [hnext]⟩]
        · simp [Lin.lin_node, par_comp_lab_root]
          -- Need to prove both operands of nondet_min are always equal...
          sorry
        · sorry
        · sorry
      · sorry
      · sorry
      · sorry


      /-
        rw [nondet_lin_node_congr _ hnext (fun _ hx ↦ hx.1)]
      -- Case 1: Next node is the root
      · simp only [Lpo.lin_node]
        rw [nondet_singleton, par_comp_lab_root]; simp only
        have h {t : Finset Node} (hr : root ∉ t) : s ∩ t = (s.erase root) ∩ t := by
          refine ((Finset.erase_inter _ _ _).trans (Finset.erase_eq_of_not_mem ?_)).symm
          intro hc; exact hr (Finset.mem_of_mem_inter_right hc)
        have h₁ : s ∩ α.nodes_finset = (s.erase root) ∩ α.nodes_finset :=
          h ((Set.Finite.mem_toFinset _).mp.mt hr₁)
        have h₂ : s ∩ β.nodes_finset = (s.erase root) ∩ β.nodes_finset :=
          h ((Set.Finite.mem_toFinset _).mp.mt hr₂)
        rw [h₁, h₂]
        refine hind (s.erase root)  ?_ hτ hτ₁ hτ₂
        refine Finset.erase_ssubset ?_; exact (ge_of_eq hnext (Set.mem_singleton root)).1
      -- Case 2: Next comes from either α or β
      · rw [minProb_nondet, iInf_subtype]
        refine le_of_le_of_eq ?_
          (iInf_congr fun i ↦
            (iInf_congr_Prop (Set.mem_union i _ _) fun _ ↦ rfl).trans
            iInf_or
            ).symm
        rw [iInf_inf_eq, iInf_subtype', iInf_subtype']
        -- The min prob is the min of the probability from either executing α or β.
        -- We split the two cases to handle them separately
        refine le_of_eq_of_le (inf_idem _).symm (inf_le_inf ?_ ?_)
        · nth_rw 1 [Lpo.lin_rec]; simp only [hne, ↓reduceIte]
          rw [minProb_nondet]
          refine le_of_eq_of_le (iInf_next_mul hne) ?_
          refine iInf_mono fun ⟨y, hy⟩ ↦ ?_
          exact
            par_comp_inductive_step hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂ hind
        · nth_rw 2 [Lpo.lin_rec]
          simp only [↓reduceIte, hne']
          rw [minProb_nondet]
          refine le_of_eq_of_le (mul_iInf_next hne') ?_
          refine iInf_mono fun ⟨y, hy⟩ ↦ ?_
          exact
            par_comp_inductive_step' hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂ hind
      -- Case 3: Next comes from α (β is empty)
      · nth_rw 1 [Lpo.lin_rec]; simp only [↓reduceIte, hne]
        rw [minProb_nondet, minProb_nondet]
        refine le_of_eq_of_le (iInf_next_mul hne) ?_
        refine iInf_mono fun ⟨y, hy⟩ ↦ ?_
        exact
          par_comp_inductive_step hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂ hind
      -- Case 4: Next comes from β (α is empty)
      · nth_rw 2 [Lpo.lin_rec]; simp only [hne, ↓reduceIte]
        rw [minProb_nondet, minProb_nondet]
        refine le_of_eq_of_le (mul_iInf_next hne) ?_
        refine iInf_mono fun ⟨y, hy⟩ ↦ ?_
        exact
          par_comp_inductive_step' hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂ hind
      -/
