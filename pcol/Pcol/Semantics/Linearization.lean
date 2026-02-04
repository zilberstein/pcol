import Init.Prelude
import Pcol.Semantics.Basic
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Isomorphism

import Pcol.Dist

open Classical
open ENNReal

namespace Lin
variable {α act test l : Type}
variable [Bot l]
variable {δ m : Type → Type}
variable [InvSem δ act α (m α)] [Sem test α Bool]
variable [CompatibleProj (Invariant δ α) (Invariant δ α)]
variable [Check m δ α] [Lin m]
variable [∀ {α}, Preorder (m α)] [∀ {α}, OrderBot (m α)]

-- Linearization state:
--   * underlying state
--   * current rely invariant probability
--   * current local scheduler steps taken so far
abbrev State (δ : Type → Type) (α : Type) := α × (ℕ → ENNReal) × ℕ × Invariant δ α

namespace State
  variable {δ : Type → Type} {α : Type}

  def state (st : State δ α) : α := st.1

  def prob (st : State δ α) : (ℕ → ENNReal) := st.2.1

  def step (st : State δ α) : ℕ := st.2.2.1

  def curr_inv (st : State δ α) : Invariant δ α := st.2.2.2
end State

def next (a : Lpofin l) (s : Finset Node) : Set Node :=
  { x | x ∈ s ∧ x ∈ a.nodes ∧ ∀ y, a.rel y x → y ∉ s }

lemma next_empty {a : Lpofin l} :
    next a ∅ = ∅ := by
  ext x; constructor
  · rintro ⟨⟨⟩, _⟩
  · rintro ⟨⟩

noncomputable def filter_by_outcome
    (α : Lpofin l) (s : Finset Node) (x : Node) (b : Bool) : Finset Node :=
  s.filter fun z ↦
    Form.sat
      ((α.form z).and
        (bif b then (Form.literal x) else (Form.literal x).not))

mutual
  noncomputable def lin_rec
    (ℛ ℐ 𝒢 : Invariant δ α)
    (a : Lpofin (Label act test)) (s : Finset Node)
    (st : State δ α) : m (State δ α) :=
    have ⟨σ, prob, step, curr_inv⟩ := st
    if s = ∅ then
      Check.check 𝒢 st.state >>= fun σ' => pure (σ', prob, step, curr_inv)
    else
      Lin.nondet fun x : next a s =>
        Lin.nondet_min
          (st.prob 0)
          (lin_node ℛ ℐ 𝒢 a (s.erase x) x.val (σ, fun _ => 1, Nat.succ step, ℛ ▹ ℐ))
          (lin_node ℛ ℐ 𝒢 a (s.erase x) x.val (σ, fun k => st.prob (Nat.succ k), Nat.succ step, curr_inv))
    termination_by (s.card, 0)
    decreasing_by
      · left; apply Finset.card_erase_lt_of_mem x.property.1
      · left; apply Finset.card_erase_lt_of_mem x.property.1

  noncomputable def lin_node
      (ℛ ℐ 𝒢 : Invariant δ α)
      (a : Lpofin (Label act test)) (s : Finset Node) (x : Node)
      (st : State δ α) : m (State δ α) :=
    have h (r : Bool) : (filter_by_outcome a s x r).card ≤ s.card := by apply Finset.card_filter_le
    have ⟨σ, prob, step, curr_inv⟩ := st
    match a.lab x with
    | Label.lab_bot => ⊥
    | Label.lab_fork => lin_rec ℛ ℐ 𝒢 a s st
    | Label.lab_act ac =>
      InvSem.inv_sem ac st.curr_inv st.state >>= fun σ' =>
         lin_rec ℛ ℐ 𝒢 a s (σ', prob, step, curr_inv)
    | Label.lab_test b =>
      have r := Sem.sem b st.state
      lin_rec ℛ ℐ 𝒢 a (filter_by_outcome a s x r) st
    termination_by (s.card, 1)
    decreasing_by
    · right ; simp
    · right ; simp
    · cases lt_or_eq_of_le (h r) with
      | inl h => left; exact h
      | inr h => rw [h] ; right ; simp
end

noncomputable def lin
  (ℛ ℐ 𝒢 : Invariant δ α) (pₖ : ℕ → ENNReal)
  (a : Lpofin (Label act test)) (init: α × ℕ) : m (α × ℕ) :=
    (lin_rec ℛ ℐ 𝒢 a a.nodes_finset (init.1, pₖ, init.2, ℐ)) >>=
      fun st => pure (st.state, st.step)

lemma next_iso [LE l]
  {s t : Finset Node} {a b : Lpofin l}
  (hle : a ≤ b)
  (hst : s = t ∩ a.nodes_finset)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s) :
  next a s = next b t := by {
    have hsub : s ⊆ t := by rw [hst]; exact Finset.inter_subset_left
    have ha : s ⊆ a.nodes_finset := by rw [hst]; exact Finset.inter_subset_right
    unfold Lpofin.nodes at *
    unfold next; ext x; simp; constructor
    · intro ⟨hx, hxa, hr⟩;
      have hxb : x ∈ b.nodes := by
        simp [Lpofin.nodes] at *; exact hle.nodes hxa
      refine ⟨hsub hx, hxb, fun y hy hc => ?_⟩
      have hxa := (Set.Finite.mem_toFinset _).1 (ha hx)
      have hya := hle.downcl _ hxa y hy
      unfold Lpofin.rel at hy
      rw [← hle.rel _ hya _ hxa] at hy
      have hys : y ∈ s := by {
        rw [hst]
        exact Finset.mem_inter.2 ⟨hc, (Set.Finite.mem_toFinset a.property).2 hya⟩
      }
      exact hr y hy hys
    · intro ⟨hx, hxb, hr⟩; refine ⟨?_, ?_, fun y hy hc => ?_,⟩
      · sorry
      · sorry
      · rcases a.val.property.rel_dom hy with ⟨hya, hxa⟩
        unfold Lpofin.rel at *; rw [hle.rel _ hya _ hxa] at hy
        exact hr y hy (hsub hc)
  }

lemma lin_node_mono
  [Preorder act] [∀ {α}, Preorder (m α)] [Preorder test] [∀ {α}, OrderBot (m α)]
  [LawfulInvSem δ act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  {s t : Finset Node} {a b : Lpofin (Label act test)}
  {ℛ ℐ 𝒢 : Invariant δ α} {x : Node}
  (hst : s = t ∩ a.nodes_finset)
  (hcl : a.rel.IsUpClosed s)
  (hbot : ∀ y ∈ a.nodes, y ≠ x → a.lab y = ⊥ → y ∈ s)
  (hind : ∀ s' ⊆ s, ∀ t' : Finset Node,
          s' = t' ∩ a.nodes_finset →
          a.rel.IsUpClosed s' →
          (∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s') →
          (lin_rec ℛ ℐ 𝒢 a s' : State δ α → m (State δ α)) ≤ lin_rec ℛ ℐ 𝒢 b t')
  (hle : a ≤ b) :
  ∀ st : State δ α,
    (lin_node ℛ ℐ 𝒢 a s x st : m (State δ α)) ≤ lin_node ℛ ℐ 𝒢 b t x st := by
    intros st
    unfold lin_node
    match hl : a.lab x with
    | Label.lab_bot =>
      simp
    | Label.lab_fork =>
      have hlle := hle.lab x; unfold Lpofin.lab at *
      simp [hl, LE.le] at hlle; rw [hlle]; simp
      apply hind ; all_goals try first | assumption | simp
      intros y hin hy ; by_cases heq : y = x
      · rw [heq] at hy ; rw [hy] at hl ; contradiction
      · exact hbot _ hin heq hy
    | Label.lab_act ac =>
      have hlx := hle.lab x; unfold Lpofin.lab at *; rw [hl] at hlx
      rcases lab_is_act_le hlx with ⟨a', hbx, hxle⟩; rw [hbx] ; simp
      apply le_trans
      · apply LawfulLin.bind_mono_left
        apply LawfulInvSem.inv_sem_mono _ _ hxle
      · apply LawfulLin.bind_mono_right
        · refine Pi.le_def.2 ?_ ; intro
          apply hind ; all_goals try first | assumption | simp
          intros y hin hy ; by_cases heq : y = x
          · rw [heq] at hy ; rw [hy] at hl ; contradiction
          · exact hbot _ hin heq hy
    | Label.lab_test bb =>
        have hlx := hle.lab x; unfold Lpofin.lab at *; rw [hl] at hlx
        rcases lab_is_test_le hlx with ⟨b', hbx, hxle⟩; rw [hbx]
        apply hind
        · sorry
        -- Need to prove that a.form = b.form
        · sorry
        · sorry
        · sorry

lemma lin_rec_mono
  [Preorder act] [Preorder test]
  [LawfulInvSem δ act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  {s t : Finset Node} {a b : Lpofin (Label act test)} {ℛ ℐ 𝒢 : Invariant δ α}
  (hst : s = t ∩ a.nodes_finset)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s)
  (hle : a ≤ b) :
  (lin_rec ℛ ℐ 𝒢 a s : State δ α → m (State δ α)) ≤ lin_rec ℛ ℐ 𝒢 b t := by
   induction s using Finset.strongInduction generalizing t with
   | H s hind =>
    refine Pi.le_def.2 ?_; intro st; unfold lin_rec
    by_cases h : s = ∅
    · subst h; simp;
      have ht : t = ∅ := sorry
      simp [ht]
    · have ht : t ≠ ∅ := by sorry
      simp [eq_false h, eq_false ht]
      rw [← next_iso hle hst hscl hbot]
      refine LawfulLin.nondet_mono ?_
      refine Pi.le_def.2 ?_; intro ⟨x, hx⟩
      have hst' : s.erase x = (t.erase x) ∩ a.nodes_finset :=
        by rw [Finset.erase_inter, ← hst]
      have hcl' : a.rel.IsUpClosed (s.erase x) := by
        intro y hy z hz
        -- y ∈ s and y ≠ x, since y < z, and x ∈ next a s, then x ≠ z
        -- so z ∈ s since s is up closed
        sorry
      have hbot' : ∀ y ∈ a.nodes, y ≠ x → a.lab y = ⊥ → y ∈ (s.erase x) := by
        intro y hy hne hyb
        refine Finset.mem_erase.2 ⟨?_,?_⟩
        · simp ; intros hc ; contradiction
        · exact hbot _ hy hyb
      apply LawfulLin.nondet_min_mono (st.prob 0)
      · apply lin_node_mono hst' hcl' hbot' ?_ hle
        intros s' hsub
        apply hind
        sorry
      · apply lin_node_mono hst' hcl' hbot' ?_ hle
        intros s' hsub
        apply hind
        sorry

theorem lin_mono
  [PartialOrder act] [PartialOrder test]
  [LawfulInvSem δ act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  (ℛ ℐ 𝒢 : Invariant δ α) (pₖ : ℕ → ENNReal) :
  Monotone (lin ℛ ℐ 𝒢 pₖ : Lpofin (Label act test) → (α × ℕ) → m (α × ℕ)) := by
    unfold lin ; intro α β hle
    refine Pi.le_def.2 ?_
    intros ; simp
    apply le_trans
    · apply LawfulLin.bind_mono_left
      · apply lin_rec_mono (t := β.nodes_finset)
        · unfold Lpofin.nodes_finset
          rw [Finset.inter_eq_right.2]
          simp
          apply hle.nodes
        · intro _ _ y hr; simp [Lpofin.nodes, Lpo.nodes]
          exact (Set.Finite.mem_toFinset _).mpr (α.val.property.rel_dom hr).2
        · intro _ hx _; exact (Set.Finite.mem_toFinset _).mpr hx
        · apply hle
    · simp

lemma lin_rec_iso
  [Preorder act] [Preorder test]
  [LawfulInvSem δ act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  {ℛ ℐ 𝒢 : Invariant δ α}
  {a : Lpofin (Label act test)} {e : Equiv.Perm Node} {s : Finset Node} :
  (lin_rec ℛ ℐ 𝒢 a s : State δ α →  m (State δ α)) = lin_rec ℛ ℐ 𝒢 (a.permute e) (s.image e) := by
  induction s using Finset.strongInduction with
  | H s hind =>
    ext st; unfold lin_rec; by_cases h : s = ∅
    · subst h; simp
    · simp only [h, ↓reduceIte, Finset.image_eq_empty]
      sorry

lemma lin_iso
  [Preorder act] [Preorder test]
  [LawfulInvSem δ act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  {ℛ ℐ 𝒢 : Invariant δ α} {pₖ : ℕ → ENNReal}
  {a b : Lpofin (Label act test)} (h : a ≈ b) :
  (lin ℛ ℐ 𝒢 pₖ a : α × ℕ →  m (α × ℕ)) = lin ℛ ℐ 𝒢 pₖ b := by
  unfold lin; rcases h with ⟨e, h⟩
  funext
  sorry
  /-
  refine Eq.trans lin_rec_iso (congr_arg₂ _ (Subtype.ext h) ?_)
  have hn := congr_arg Lpo.nodes h; simp [permute, Lpo.nodes] at hn
  have _ : Fintype ↑(e '' a.val.val.nodes) := by
    unfold Lpo.nodes; rw [hn]; exact b.property.fintype
  have _ : Fintype ↑(b.val.val.nodes) := b.property.fintype
  refine (Set.Finite.toFinset_image _ _ ?_).symm.trans ?_
  · unfold Lpo.nodes; rw [hn]; exact b.property
  · unfold Lpofin.nodes_finset; unfold Set.Finite.toFinset
    refine @Set.toFinset_congr _ _ _ ?_ ?_ hn
  -/

end Lin
