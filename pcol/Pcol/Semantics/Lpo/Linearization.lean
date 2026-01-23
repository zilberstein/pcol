import Init.Prelude
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Isomorphism

import Pcol.Dist

open Classical
open ENNReal

inductive Label (act : Type) (test : Type)
  | lab_bot : Label act test
  | lab_fork : Label act test
  | lab_act : act → Label act test
  | lab_test : test → Label act test

instance {act test : Type} : Bot (Label act test) where
  bot := Label.lab_bot

instance {act test : Type} [LE act] [LE test] : LE (Label act test) where
  le l1 l2 :=
    match l1 with
    | Label.lab_bot => True
    | Label.lab_fork => l2 = Label.lab_fork
    | Label.lab_act a =>
      match l2 with
      | Label.lab_act a' => a ≤ a'
      | _ => False
    | Label.lab_test b =>
      match l2 with
      | Label.lab_test b' => b ≤ b'
      | _ => False

lemma lab_is_act_le {act test : Type} {a : act} {l : Label act test}
  [Preorder act] [Preorder test]
  (hle : Label.lab_act a ≤ l) :
  ∃ a', l = Label.lab_act a' ∧ a ≤ a' := by {
    match l with
    | Label.lab_bot => simp [LE.le] at hle
    | Label.lab_fork => simp [LE.le] at hle
    | Label.lab_act a' => simp [LE.le] at hle; exact ⟨a', rfl, hle⟩
    | Label.lab_test _ => simp [LE.le] at hle
  }

lemma lab_is_test_le {act test : Type} {b : test} {l : Label act test}
  [Preorder act] [Preorder test]
  (hle : Label.lab_test b ≤ l) :
  ∃ b', l = Label.lab_test b' ∧ b ≤ b' := by {
    match l with
    | Label.lab_bot => simp [LE.le] at hle
    | Label.lab_fork => simp [LE.le] at hle
    | Label.lab_act _ => simp [LE.le] at hle
    | Label.lab_test b' => simp [LE.le] at hle; exact ⟨b', rfl, hle⟩
  }

instance {act test : Type} [Preorder act] [Preorder test] : Preorder (Label act test) where
  le_refl := by intro l; simp [LE.le]; cases l; all_goals simp
  le_trans := by {
    intro l₁ l₂ l₃ h12 h23; simp [LE.le]
    match l₁ with
    | Label.lab_bot => simp
    | Label.lab_fork =>
        simp [LE.le] at h12; simp [h12, LE.le] at h23
        exact h23
    | Label.lab_act a =>
        rcases lab_is_act_le h12 with ⟨a₂, hl₂, ha₂⟩; subst hl₂
        rcases lab_is_act_le h23 with ⟨a₃, hl₃, ha₃⟩; subst hl₃
        simp at *; exact le_trans ha₂ ha₃
    | Label.lab_test b =>
        rcases lab_is_test_le h12 with ⟨b₂, hl₂, hb₂⟩; subst hl₂
        rcases lab_is_test_le h23 with ⟨b₃, hl₃, hb₃⟩; subst hl₃
        simp at *; exact le_trans hb₂ hb₃
  }

instance {act test : Type} [PartialOrder act] [PartialOrder test] : PartialOrder (Label act test) where
  le_antisymm l₁ l₂ h12 h21 := by {
    cases l₁ <;> cases l₂ <;> simp [LE.le] at *
    · exact le_antisymm h12 h21
    · exact le_antisymm h12 h21
  }

instance {act test : Type} [LE act] [LE test] : OrderBot (Label act test) where
  bot_le _ := True.intro

class Linearizable (t : Type → Type)
  [Monad t] [∀ {β : Type}, Preorder (t β)]
  where
  -- Nondeterministic choice with minimum probability `p` for
  -- first choice (so that nondet_min 1 m₁ m₂ = m₁)
  nondet_min {α : Type} : ENNReal → t α → t α → t α

  -- Nondeterministic choice (TODO: derive from previous)
  nondet {ι α : Type} : (ι → t α) → t α

  nondet_min_mono {α : Type} : ∀ {m₁ m₂ t₁ t₂ : t α} (p : ENNReal),
    m₁ ≤ m₂ → t₁ ≤ t₂ → nondet_min p m₁ t₁ ≤ nondet_min p m₂ t₂

  nondet_mono {ι α : Type} : Monotone (nondet : (ι → t α) → t α)

  bind_mono {β γ : Type} : ∀ {m₁ m₂ : t β} {k₁ k₂ : β → t γ},
    m₁ ≤ m₂ → k₁ ≤ k₂ → bind m₁ k₁ ≤ bind m₂ k₂
 --  bind_additivity : ∀ f s, bind (nondet s) f = nondet (Finset.image (fun x => bind x f) s)


class Sem (c : Type) (in_type out_type : Type)
  extends PartialOrder c
  where
    sem : c → Finset in_type → in_type → out_type
    sem_mono [Preorder out_type] (s : in_type) (inv : Finset in_type) : Monotone (sem · inv s)

noncomputable def check {t : Type → Type} {α : Type} [Monad t] [∀ {β}, Bot (t β)]
  (a: α) (s: Finset α) : t α := if a ∈ s then pure a else ⊥

namespace Lpo

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
    [Sem act α (t α)] [Sem test α Bool] [Monad t] [∀ {β : Type}, Preorder (t β)]
    [Linearizable t] [∀ {β}, Bot (t β)]
    (rely: Finset α) (inv: Finset α) (guar: Finset α)
    (a : Lpofin (Label act test)) (s : Finset Node)
    (st : LinState α) : t (LinState α) :=
    if s = ∅ then
      ({st with state := ·}) <$> check st.state guar
    else
      Linearizable.nondet fun x : next a s =>
        have st' := { st with step := Nat.succ st.step }
        Linearizable.nondet_min
          (st.prob 0)
          (lin_node rely inv guar a (s.erase x) x.val {st' with prob := fun _ => 1, curr_inv := rely ∩ inv})
          (lin_node rely inv guar a (s.erase x) x.val {st' with prob := fun k => st.prob (Nat.succ k)})
    termination_by (s.card, 0)
    decreasing_by
      · left; apply Finset.card_erase_lt_of_mem x.property.1
      · left; apply Finset.card_erase_lt_of_mem x.property.1

  noncomputable def lin_node {t : Type → Type} {α act test: Type}
      [Sem act α (t α)] [Sem test α Bool] [Monad t] [∀ {β : Type}, Preorder (t β)]
      [Linearizable t] [∀ {β}, Bot (t β)]
      (rely: Finset α) (inv: Finset α) (guar: Finset α)
      (a : Lpofin (Label act test)) (s : Finset Node) (x : Node)
      (st : LinState α) : t (LinState α) :=
    have h (r : Bool) : (filter_by_outcome a s x r).card ≤ s.card := by apply Finset.card_filter_le
    match a.lab x with
    | Label.lab_bot => ⊥
    | Label.lab_fork => lin_rec rely inv guar a s st
    | Label.lab_act ac =>
      Sem.sem ac st.curr_inv st.state >>= (lin_rec rely inv guar a s {st with state := ·})
    | Label.lab_test b =>
      have r := Sem.sem b st.curr_inv st.state
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
  [Sem act α (t α)] [Sem test α Bool] [Monad t] [∀ {β : Type}, Preorder (t β)]
  [Linearizable t] [∀ {β}, Bot (t β)]
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
  [Monad m] [Sem act α (m α)] [Sem test α Bool] [∀ β, Preorder (m β)]
  [∀ β, OrderBot (m β)] [Linearizable m]
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
  ∀ st : LinState α, (lin_node rely inv guar a s x st : m (LinState α)) ≤ lin_node rely inv guar b t x st := by
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
      rcases lab_is_act_le hlx with ⟨a', hbx, hxle⟩; rw [hbx]
      refine Linearizable.bind_mono (Sem.sem_mono (c := act) st.state st.curr_inv hxle) ?_
      refine Pi.le_def.2 ?_ ; intro
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
  [Monad m] [Sem act α (m α)] [Sem test α Bool] [∀ β, Preorder (m β)]
  [∀ β, OrderBot (m β)] [Linearizable m]
  {s t : Finset Node} {a b : Lpofin (Label act test)} {rely inv guar : Finset α}
  (hst : s = t ∩ a.nodes_finset)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s)
  (hle : a ≤ b) :
  (lin_rec rely inv guar a s : LinState α → m (LinState α)) ≤ lin_rec rely inv guar b t := by
   induction s using Finset.strongInduction generalizing t with
   | H s hind =>
    refine Pi.le_def.2 ?_; intro st; unfold Lpo.lin_rec
    by_cases h : s = ∅
    · subst h; simp;
      have ht : t = ∅ := sorry
      simp [ht]
    · have ht : t ≠ ∅ := by sorry
      simp [eq_false h, eq_false ht]
      rw [← next_iso hle hst hscl hbot]
      refine Linearizable.nondet_mono ?_
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
      refine Linearizable.nondet_min_mono (st.prob 0) ?_ ?_
      · apply lin_node_mono hst' hcl' hbot' ?_ hle
        intros s' hsub
        apply hind
        sorry
      · apply lin_node_mono hst' hcl' hbot' ?_ hle
        intros s' hsub
        apply hind
        sorry

theorem lin_mono {m : Type → Type} {α act test : Type}
  [Monad m] [Sem act α (m α)] [Sem test α Bool] [∀ β, PartialOrder (m β)]
  [∀ β, OrderBot (m β)] [Linearizable m]
  (rely inv guar: Finset α) (pₖ : ℕ → ENNReal) :
  Monotone (lin rely inv guar pₖ : Lpofin (Label act test) → (α × ℕ) → m (α × ℕ)) := by
    unfold lin ; intro α β hle
    refine Pi.le_def.2 ?_
    intros ; refine Linearizable.bind_mono ?_ ?_
    · refine lin_rec_mono ?_ ?_ ?_ hle ?_
      · unfold Lpofin.nodes_finset; refine Eq.symm (Finset.inter_eq_right.2 ?_)
        simp [hle.nodes]
      · intro _ _ y hr; simp [Lpofin.nodes, Lpo.nodes]
        exact (Set.Finite.mem_toFinset _).mpr (α.val.property.rel_dom hr).2
      · intro _ hx _; exact (Set.Finite.mem_toFinset _).mpr hx
    · simp

lemma lin_rec_iso {m : Type → Type} {α act test : Type}
    [Monad m] [Sem act α (m α)] [Sem test α Bool] [∀ β, Preorder (m β)]
    [∀ {β}, OrderBot (m β)] [Linearizable m]
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
    [Monad m] [Sem act α (m α)] [Sem test α Bool] [∀ β, Preorder (m β)]
    [∀ {β}, OrderBot (m β)] [Linearizable m]
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
end Lpo
