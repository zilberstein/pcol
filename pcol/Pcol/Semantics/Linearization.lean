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

def next {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) : Set Node :=
  { x | x ∈ s ∧ x ∈ a.nodes ∧ ∀ y, a.rel y x → y ∉ s }

lemma next_empty {l : Type} [Bot l] {a : Lpofin l} :
    next a ∅ = ∅ := by
  ext x; constructor
  · rintro ⟨⟨⟩, _⟩
  · rintro ⟨⟩

noncomputable def filter_by_outcome {l : Type} [Bot l]
    (α : Lpofin l) (s : Finset Node) (x : Node) (b : Bool) : Finset Node :=
  s.filter fun z ↦
    Form.sat
      ((α.form z).and
        (bif b then (Form.literal x) else (Form.literal x).not))

-- Linearization state:
--   * underlying state
--   * current rely invariant probability
--   * current local scheduler steps taken so far
structure LinState (α : Type) where
  mk ::
  state : α
  prob : ℕ → ENNReal
  step : ℕ
  curr_inv : Finset α

mutual
  noncomputable def lin_rec {t : Type → Type} {α act test: Type}
    [InvSem act α (t α)] [Sem test α Bool]
    [Check t α] [Bot (t (LinState α))] [Lin t]
    (rely: Finset α) (inv: Finset α) (guar: Finset α)
    (a : Lpofin (Label act test)) (s : Finset Node)
    (st : LinState α) : t (LinState α) :=
    if s = ∅ then
      ({st with state := ·}) <$> Check.check guar st.state
    else
      Lin.nondet fun x : next a s =>
        have st' := { st with step := Nat.succ st.step }
        Lin.nondet_min
          (st.prob 0)
          (lin_node rely inv guar a (s.erase x) x.val {st' with prob := fun _ => 1, curr_inv := rely ∩ inv})
          (lin_node rely inv guar a (s.erase x) x.val {st' with prob := fun k => st.prob (Nat.succ k)})
    termination_by (s.card, 0)
    decreasing_by
      · left; apply Finset.card_erase_lt_of_mem x.property.1
      · left; apply Finset.card_erase_lt_of_mem x.property.1

  noncomputable def lin_node {t : Type → Type} {α act test: Type}
      [InvSem act α (t α)] [Sem test α Bool]
      [Check t α] [Lin t] [Bot (t (LinState α))]
      (rely: Finset α) (inv: Finset α) (guar: Finset α)
      (a : Lpofin (Label act test)) (s : Finset Node) (x : Node)
      (st : LinState α) : t (LinState α) :=
    have h (r : Bool) : (filter_by_outcome a s x r).card ≤ s.card := by apply Finset.card_filter_le
    match a.lab x with
    | Label.lab_bot => ⊥
    | Label.lab_fork => lin_rec rely inv guar a s st
    | Label.lab_act ac =>
      InvSem.inv_sem ac st.curr_inv st.state >>= (lin_rec rely inv guar a s {st with state := ·})
    | Label.lab_test b =>
      have r := Sem.sem b st.state
      lin_rec rely inv guar a (filter_by_outcome a s x r) st
    termination_by (s.card, 1)
    decreasing_by
    · right ; simp
    · right ; simp
    · cases lt_or_eq_of_le (h r) with
      | inl h => left; exact h
      | inr h => rw [h] ; right ; simp
end

noncomputable def lin {t : Type → Type} {α act test: Type}
  [InvSem act α (t α)] [Sem test α Bool]
  [Check t α] [Lin t] [Bot (t (LinState α))]
  (rely: Finset α) (inv: Finset α) (guar: Finset α) (pₖ : ℕ → ENNReal)
  (a : Lpofin (Label act test)) (init: α × ℕ) : t (α × ℕ) :=
    (lin_rec rely inv guar a a.nodes_finset (LinState.mk init.1 pₖ init.2 inv)) >>=
      fun st => pure (st.state, st.step)

lemma next_iso {l : Type} [Bot l] [LE l] {s t : Finset Node} {a b : Lpofin l}
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

-- lemma nondet_convert {α γ : Type} {m: Type → Type}
--   [Monad m] [∀ {β : Type}, Preorder (m β)] [Linearizable m α]
--   {s t : Set γ} {f : ↑s → m α}
--   (heq : s = t) :
--   Linearizable.nondet s f =
--   Linearizable.nondet t (cast (congrArg (· → m α) (congrArg Subtype heq)) f) := by {

--   }
lemma lin_node_mono {m : Type → Type} {α act test : Type}
  [InvSem act α (m α)] [Sem test α Bool] [Lin m] [Check m α]
  [Preorder act] [∀ {α}, Preorder (m α)] [Preorder test]
  [LawfulInvSem act α (m α)] [LawfulSem test α Bool] [LawfulLin m] [OrderBot (m (LinState α))]
  {s t : Finset Node} {a b : Lpofin (Label act test)} {rely inv guar : Finset α} {x : Node}
  (hst : s = t ∩ a.nodes_finset)
  (hcl : a.rel.IsUpClosed s)
  (hbot : ∀ y ∈ a.nodes, y ≠ x → a.lab y = ⊥ → y ∈ s)
  (hind : ∀ s' ⊆ s, ∀ t' : Finset Node,
          s' = t' ∩ a.nodes_finset →
          a.rel.IsUpClosed s' →
          (∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s') →
          (lin_rec rely inv guar a s' : LinState α → m (LinState α)) ≤ lin_rec rely inv guar b t')
  (hle : a ≤ b) :
  ∀ st : LinState α,
    (lin_node rely inv guar a s x st : m (LinState α)) ≤ lin_node rely inv guar b t x st := by
    intros st
    unfold lin_node
    match hl : a.lab x with
    | Label.lab_bot => simp
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

lemma lin_rec_mono {m : Type → Type} {α act test : Type}
  [InvSem act α (m α)] [Sem test α Bool] [Lin m] [Check m α]
  [Preorder act] [∀ {α}, Preorder (m α)] [Preorder test]
  [LawfulInvSem act α (m α)] [LawfulSem test α Bool] [LawfulLin m] [OrderBot (m (LinState α))]
  {s t : Finset Node} {a b : Lpofin (Label act test)} {rely inv guar : Finset α}
  (hst : s = t ∩ a.nodes_finset)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s)
  (hle : a ≤ b) :
  (lin_rec rely inv guar a s : LinState α → m (LinState α)) ≤ lin_rec rely inv guar b t := by
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

theorem lin_mono {m : Type → Type} {α act test : Type}
  [InvSem act α (m α)] [Sem test α Bool] [Lin m] [Check m α]
  [PartialOrder act] [∀ {α}, Preorder (m α)] [PartialOrder test]
  [LawfulInvSem act α (m α)] [LawfulSem test α Bool] [LawfulLin m]
  [OrderBot (m (LinState α))]
  (rely inv guar: Finset α) (pₖ : ℕ → ENNReal) :
  Monotone (lin rely inv guar pₖ : Lpofin (Label act test) → (α × ℕ) → m (α × ℕ)) := by
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

lemma lin_rec_iso {m : Type → Type} {α act test : Type}
  [InvSem act α (m α)] [Sem test α Bool] [Lin m] [Check m α]
  [Preorder act] [∀ {α}, Preorder (m α)] [Preorder test]
  [LawfulInvSem act α (m α)] [LawfulSem test α Bool] [LawfulLin m] [OrderBot (m (LinState α))]
  {rely inv guar : Finset α}
  {a : Lpofin (Label act test)} {e : Equiv.Perm Node} {s : Finset Node} :
  (lin_rec rely inv guar a s : LinState α →  m (LinState α)) = lin_rec rely inv guar (a.permute e) (s.image e) := by
  induction s using Finset.strongInduction with
  | H s hind =>
    ext st; unfold lin_rec; by_cases h : s = ∅
    · subst h; simp
    · simp only [h, ↓reduceIte, Finset.image_eq_empty]
      sorry

lemma lin_iso {m : Type → Type} {α act test : Type}
  [InvSem act α (m α)] [Sem test α Bool] [Lin m] [Check m α]
  [Preorder act] [∀ {α}, Preorder (m α)] [Preorder test]
  [LawfulInvSem act α (m α)] [LawfulSem test α Bool] [LawfulLin m] [OrderBot (m (LinState α))]
  {rely inv guar : Finset α} {pₖ : ℕ → ENNReal}
  {a b : Lpofin (Label act test)} (h : a ≈ b) :
  (lin rely inv guar pₖ a : α × ℕ →  m (α × ℕ)) = lin rely inv guar pₖ b := by
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
