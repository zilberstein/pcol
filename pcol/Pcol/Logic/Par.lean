import Mathlib.Data.Finset.Lattice.Basic

import Pcol.ConvexPowerset
import Pcol.ConvexPowerset.Monad

--import Pcol.Logic.Invariant
import Pcol.Logic.Mem
import Pcol.Logic.MinProb
import Pcol.Semantics.Linearization
import Pcol.Semantics.Lpo.Operations.Par

open Classical

-- An instance for linearizing into the convex powerdomain
instance : Lin C where
  nondet {ι X} (f : ι → C X) :=
    bind ⟨(Set.univ : Set (Distr ι)), sorry⟩ f

  nondet_min p S₁ S₂ :=
    ⟨ ⋃ (q : ENNReal) (_ : q ≥ p) (hq : q ≤ 1), (convex_comb S₁.1 S₂.1 q hq)
    , sorry ⟩

instance : LawfulLin C where
  nondet_mono := sorry
  nondet_min_mono := sorry
  bind_mono_left := sorry
  bind_mono_right := sorry

lemma nondet_singleton {u : Finset Var} {X : Type} {x : X} {f : ↑(Set.singleton x) → C Mem} :
    Lin.nondet f = f ⟨x, Set.mem_singleton _⟩ := sorry

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

lemma par_comp_comm {u₁ u₂ u : Finset Var} {act test : Type}
    (α : Lpofin (Label act test))
    (β : Lpofin (Label act test))
    (root : Node) :
    par_comp root α β = par_comp root β α := sorry

-- The set of next nodes in a parallel composition is either
-- 1) Only the root
-- 2) The union of (nonempty) next node sets from α and β
-- 3) The next nodes of α (if β is done executing)
-- 4) The next nodes of β (if β is done executing)
lemma next_par {u₁ u₂ u : Finset Var} {act test : Type}
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

variable {act test : Type}
  [Sem act Mem (C Mem)]
  [Check C Mem]
  [Replace C Mem]
  [Sem test Mem Bool]
  {α : Lpofin (Label act test)}
  {β : Lpofin (Label act test)}
  {root : Node}
--   (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes)
--  {inv : Finset (Mem v)}
  {rely inv guar : Finset Mem}
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
  (s : Finset Node) (σ₁ σ₂ τ : Mem) (A B : Set Mem) (pₖ : ℕ → ENNReal) (k : ℕ) (curr_inv : Finset Mem)
  /-(s : Finset Node) (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (_ : τ ∈ inv) (_ : τ₁ ∈ inv) (_ : τ₂ ∈ inv)
      (_ : α.has_inv inv) (_ : β.has_inv inv)-/ : Prop :=
  minProb (Lin.lin_rec rely inv guar (par_comp root α β ) s ⟨σ₁ ⊎ σ₂ ⊎ τ, pₖ, k, curr_inv⟩)
      (A ** B ** inv) ≥
  minProb (Lpo.lin_rec α (s ∩ α.nodes_finset) (σ₁.union τ₁ (dsj₁ hv) : Mem u₁)) (Mem.sep A ↑inv (dsj₁ hv)) *
    minProb (Lpo.lin_rec β (s ∩ β.nodes_finset) (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv))

-- The inductive step broken into its own lemma, since it needs to be invoked multiple times
 lemma par_comp_inductive_step
    {s : Finset Node} {x : Node} (hx : x ∈ Lpo.next α (s ∩ α.nodes_finset))
    (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv)
    (hinv₁ : α.has_inv inv) (hinv₂ : β.has_inv inv)
    (hind : ∀ t ⊂ s,
      ∀ (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv),
      is_indep hr₁ hr₂ hu hv hdn A B t σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂) :
    minProb (Lpo.lin_node (par_comp α β hdn hu hr₁ hr₂) s x sorry (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) ≥
    minProb (Lpo.lin_node α (s ∩ α.nodes_finset) x hx.1 (σ₁.union τ₁ (dsj₁ hv))) (Mem.sep A ↑inv (dsj₁ hv)) *
      minProb (Lpo.lin_rec β (s ∩ β.nodes_finset) (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv)) := by
  unfold Lpo.lin_node
  have hu' := hu.trans (Finset.union_comm _ _)
  have hv' := hv.trans (Finset.inter_comm _ _)
  have hlab_eq : (par_comp α β hdn hu hr₁ hr₂).lab x = upcast_lab (α.lab x) sorry := sorry -- LEMMA
  rw [hlab_eq]; cases hlab : α.lab x with
  -- Case : α.lab y = ⊥
  | lab_bot => simp only [upcast_lab, minProb_bot, zero_mul, le_refl]
  -- Case : α.lab y = Fork
  | lab_fork =>
    simp only [upcast_lab]
    have h₁ : (s ∩ α.nodes_finset).erase x = s.erase x ∩ α.nodes_finset := sorry
    have h₂ : s ∩ β.nodes_finset = s.erase x ∩ β.nodes_finset := sorry
    rw [h₁, h₂]
    refine hind (s.erase x) ?_ _ _ hτ hτ₁ hτ₂
    exact Finset.erase_ssubset (Finset.mem_of_mem_inter_left hx.1)
  -- Case : α.lab y = act
  | lab_act a =>
    simp only [upcast_lab]
    rw [union_comm_assoc hu hv]
    refine le_trans ?_
      (minProb_mono (Linearizable.bind_mono (upcast_mono (dsj₂₁ hu hv)) (le_refl _)))
    rw [bind_assoc, minProb_bind, minProb_bind]
    refine le_of_eq_of_le iInf_C_mul_minProb ?_
    have hinv : a.has_inv inv := by
      have h := hinv₁ x hx.2.1; simp only [hlab] at h; exact h
    rw [inv_sem_eq hinv hτ hτ₁]
    refine iInf₂_mono fun μ hμ ↦ ?_
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun ⟨σ, hσ⟩ ↦ ?_
    refine le_of_eq_of_le
      (mul_assoc _ _ _)
      (mul_le_mul (le_refl _) ?_ bot_le bot_le)
    have h₂ : s ∩ β.nodes_finset = s.erase x ∩ β.nodes_finset := sorry
    rw [← Finset.erase_inter, h₂]
    rw [pure_bind]
    obtain ⟨σ', τ, heq, hinv⟩ : ∃ σ' : Mem (u₁ \ v), ∃ τ : Mem v, σ = σ'.union τ (dsj₁ hv) ∧ τ ∈ inv := sorry
    simp only [heq]; rw [union_comm_assoc hu' hv']
    refine (hind (s.erase x) ?_ _ _ hinv hinv hτ₂)
    exact Finset.erase_ssubset (Finset.mem_of_mem_inter_left hx.1)
  | lab_test t =>
    simp only [upcast_lab]
    rw [union_comm_assoc hu hv]
    refine le_trans ?_
      (minProb_mono (Linearizable.bind_mono (upcast_mono_test (dsj₂₁ hu hv)) (le_refl _)))
    rw [minProb_bind, minProb_bind]
    refine le_of_eq_of_le iInf_C_mul_minProb ?_
    have hinv : t.has_inv inv := by
      have h := hinv₁ x hx.2.1; simp only [hlab] at h; exact h
    rw [inv_sem_eq_test hinv hτ hτ₁]
    refine iInf₂_mono fun μ hμ ↦ ?_
    rw [← ENNReal.tsum_mul_right]
    refine ENNReal.tsum_le_tsum fun ⟨b, hb⟩ ↦ ?_
    refine le_of_eq_of_le
      (mul_assoc _ _ _)
      (mul_le_mul (le_refl _) ?_ bot_le bot_le)
    have h₁ :
        Lpo.filter_by_outcome α (s ∩ α.nodes_finset) x b =
        (Lpo.filter_by_outcome α s x b) ∩ α.nodes_finset := by
      unfold Lpo.filter_by_outcome
      rw [← Finset.erase_inter]; exact (Finset.filter_inter _ _ _).symm
    have h₂ :
      s ∩ β.nodes_finset =
      (Lpo.filter_by_outcome α s x b) ∩ β.nodes_finset := sorry
    have h₃ :
        Lpo.filter_by_outcome (par_comp α β hdn hu hr₁ hr₂) s x b =
        Lpo.filter_by_outcome α s x b := by sorry
    rw [h₁, h₂, h₃]
    rw [union_comm_assoc hu' hv']
    refine (hind _ ?_ _ _ hτ hτ₁ hτ₂)
    refine Finset.ssubset_of_subset_of_ssubset (Finset.filter_subset _ _) ?_
    exact (Finset.erase_ssubset (Finset.mem_of_mem_inter_left hx.1))

-- Version of the previous lemma but swapped so that β is taking a step instead of α
lemma par_comp_inductive_step'
    {s : Finset Node} {x : Node} (hx : x ∈ Lpo.next β (s ∩ β.nodes_finset))
    (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv)
    (hinv₁ : α.has_inv inv) (hinv₂ : β.has_inv inv)
    (hind : ∀ t ⊂ s,
      ∀ (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
         (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv),
      is_indep hr₁ hr₂ hu hv hdn A B t σ₁ σ₂ hτ hτ₁ hτ₂ hinv₁ hinv₂) :
    minProb (Lpo.lin_node (par_comp α β hdn hu hr₁ hr₂) s x sorry (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) ≥
    minProb (Lpo.lin_rec α (s ∩ α.nodes_finset) (σ₁.union τ₁ (dsj₁ hv))) (Mem.sep A ↑inv (dsj₁ hv)) *
      minProb (Lpo.lin_node β (s ∩ β.nodes_finset) x hx.1 (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv)) := by
  rw [mul_comm, union_comm_assoc hu hv, sep_comm_assoc hu hv, par_comp_comm hu]
  have hu' := hu.trans (Finset.union_comm _ _)
  have hv' := hv.trans (Finset.inter_comm _ _)
  refine
    par_comp_inductive_step hr₂ hr₁ hu' hv' hdn.symm B A hx σ₂ σ₁ hτ hτ₂ hτ₁ hinv₂ hinv₁ ?_
  intro t ht σ₁ σ₂ τ τ₁ τ₂ hτ hτ₁ hτ₂; unfold is_indep
  rw [par_comp_comm,
      union_comm_assoc (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _)),
      sep_comm_assoc (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _)),
      mul_comm]
  exact hind t ht σ₂ σ₁ hτ hτ₂ hτ₁

-- We need this annoying lemma to make the dependent types work out
lemma nondet_lin_node_congr {u : Finset Var} {act test : Type}
    [Sem act (Mem u) (C (Mem u))]
    [Sem test (Mem u) Bool]
    (α : Lpofin (Label (WithInv act u) (WithInv test u)))
    {i j : Set Node} {s : Finset Node} {σ : Mem u}
    (h : i = j) (hi : i ⊆ s) :
    (Linearizable.nondet fun x : ↑i ↦ Lpo.lin_node α s x.val (hi x.property) σ : C (Mem u)) =
    (Linearizable.nondet fun x : ↑j ↦ Lpo.lin_node α s x.val (hi ((congrArg₂ Membership.mem h rfl).mpr x.property)) σ) := by
  simp only [Lpo.lin_node]; rw [h]

-- Lemma C.3 from POPL'26
theorem par_comp_fin
    {σ₁ : Mem (u₁ \ v)} {σ₂ : Mem (u₂ \ v)} {τ τ₁ τ₂ : Mem v}
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv)
    (hinv₁ : α.has_inv inv) (hinv₂ : β.has_inv inv) :
    minProb
      (Lpo.lin
        (par_comp α β hdn hu hr₁ hr₂)
        (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) ≥
      minProb (Lpo.lin α (σ₁.union τ₁ (dsj₁ hv))) (Mem.sep A ↑inv (dsj₁ hv)) *
      minProb (Lpo.lin β (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv)) := by
  unfold Lpo.lin
  generalize hs : (par_comp α β hdn hu hr₁ hr₂).nodes_finset = s
  have h₁ : α.nodes_finset = s ∩ α.nodes_finset := sorry; rw [h₁]
  have h₂ : β.nodes_finset = s ∩ β.nodes_finset := sorry; rw [h₂]
  clear h₁ h₂ hs; revert σ₁ σ₂ τ τ₁ τ₂
  induction s using Finset.strongInduction with
  | H s hind =>
    intro σ₁ σ₂ τ τ₁ τ₂ hτ hτ₁ hτ₂
    by_cases hemp : s = ∅
    -- Base Case: No more nodes to schedule
    · unfold Lpo.lin_rec; simp only [hemp, ↓reduceIte, Finset.empty_inter, minProb_pure, Mem.union_mem]
      by_cases h₁ : σ₁ ∈ A <;> by_cases h₂ : σ₂ ∈ B <;>
        simp only [h₁, h₂, Finset.mem_coe.mpr hτ, Finset.mem_coe.mpr hτ₁, Finset.mem_coe.mpr hτ₂,
          and_true, and_false, ↓reduceIte, and_self, mul_zero, mul_one, le_refl]
    -- Inductive Case
    · nth_rw 1 [Lpo.lin_rec]; simp only [hemp, ↓reduceIte]
      rcases next_par α β hdn hu hr₁ hr₂ s with hnext | ⟨hnext, hne, hne'⟩ | ⟨hnext, hne⟩ | ⟨hnext, hne⟩ <;>
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
