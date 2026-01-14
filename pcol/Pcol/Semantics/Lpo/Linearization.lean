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
  -- Nondeterministic choice with minimum probability
  nondet_min {ι α : Type} : ENNReal → (ι → t α) → t α

  -- Nondeterministic choice (TODO: derive from previous)
  nondet {ι α : Type} : (ι → t α) → t α

  nondet_mono {ι α : Type} : Monotone (nondet : (ι → t α) → t α)
  bind_mono {β γ : Type} : ∀ {m₁ m₂ : t β} {k₁ k₂ : β → t γ},
    m₁ ≤ m₂ → k₁ ≤ k₂ → bind m₁ k₁ ≤ bind m₂ k₂
 --  bind_additivity : ∀ f s, bind (nondet s) f = nondet (Finset.image (fun x => bind x f) s)

class Sem (c : Type) (in_type out_type : Type)
  extends PartialOrder c
  where
    sem : c → Finset in_type → in_type → out_type
    sem_mono [Preorder out_type] (s : in_type) : Monotone (sem · · s)

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

mutual
  noncomputable def lin_rec {t : Type → Type} {α act test: Type}
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
    [Linearizable t] [∀ {β}, Bot (t β)]
    (rely: Finset α) (inv: Finset α)
    (a : Lpofin (Label act test)) (s : Finset Node)
    (st : α × (ℕ → ENNReal)) : t (α × (ℕ → ENNReal)) :=
    if s = ∅ then
      pure st
    else
      Linearizable.nondet fun x : next a s => lin_node rely inv a (s.erase x) x.val st
    termination_by (s.card, 0)
    decreasing_by
      · left; apply Finset.card_erase_lt_of_mem x.property.1

  noncomputable def lin_act {t : Type → Type} {α act: Type}
      [Sem act α (t α)]
      [Monad t] [∀ {β : Type}, Preorder (t β)] [Linearizable t]
      (rely: Finset α) (inv: Finset α)
      (ac : act)
      (st : α × (ℕ → ENNReal)) : t (α × (ℕ → ENNReal)) :=
      have j := sorry
      Linearizable.nondet_min (st.2 j) fun x =>
        if x then
          (fun st' => (st', fun _ => 1)) <$> Sem.sem ac (rely ∩ inv) st.1 -- TODO: is intersection what we want here?
        else
          (fun st' => (st', fun k => st.2 (Nat.succ k))) <$> Sem.sem ac inv st.1

  noncomputable def lin_node {t : Type → Type} {α act test: Type}
      [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
      [Linearizable t] [∀ {β}, Bot (t β)]
      (rely: Finset α) (inv: Finset α)
      (a : Lpofin (Label act test)) (s : Finset Node) (x : Node)
      (st : α × (ℕ → ENNReal)) : t (α × (ℕ → ENNReal)) :=
    have h (r : Bool) : (filter_by_outcome a s x r).card ≤ s.card := by apply Finset.card_filter_le
    match a.lab x with
    | Label.lab_bot => ⊥
    | Label.lab_fork => lin_rec rely inv a s st
    | Label.lab_act ac => bind (lin_act rely inv ac st) (lin_rec rely inv a s)
    | Label.lab_test b =>
        bind (Sem.sem b sorry st.1)
          fun r => lin_rec rely inv a (filter_by_outcome a s x r) st
    termination_by (s.card, 1)
    decreasing_by
    · right ; simp
    · right ; simp
    · cases lt_or_eq_of_le (h r) with
    | inl h => left; exact h
    | inr h => rw [h] ; right ; simp
end

noncomputable def lin {t : Type → Type} {α act test: Type}
  [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
  [Linearizable t] [∀ {β}, Bot (t β)]
  (rely: Finset α) (inv : Finset α)
  (a : Lpofin (Label act test)) (st : α) (pₖ : ℕ → ENNReal) : t α :=
    (fun (st, _) => st) <$> (lin_rec rely inv a a.nodes_finset (st, pₖ))

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

theorem lin_rec_mono {m : Type → Type} {α act test : Type}
  [Monad m] [Sem act α (m α)] [Sem test α (m Bool)] [∀ β, Preorder (m β)]
  [OrderBot (m α)] [Linearizable m]
  {s t : Finset Node} {a b : Lpofin (Label act test)}
  (hst : s = t ∩ a.nodes_finset)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s)
  (hle : a ≤ b) :
  (lin_rec a s : α → m α) ≤ lin_rec b t := by {
    induction s using Finset.strongInduction generalizing t with
    | H s hind =>
      refine Pi.le_def.2 ?_; intro st; unfold Lpo.lin_rec
      have heq := next_iso hle hst hscl hbot
      by_cases h : s = ∅
      · subst h; simp;
        have ht : t = ∅ := sorry
        simp [ht]
      · have ht : t ≠ ∅ := by sorry
        simp [eq_false h, eq_false ht, lin_node]
        rw [← next_iso hle hst hscl hbot]
        refine Linearizable.nondet_mono ?_
        refine Pi.le_def.2 ?_; intro ⟨x, hx⟩
        match hl : a.lab x with
        | Label.lab_bot => simp
        | Label.lab_fork =>
            have hlle := hle.lab x; unfold Lpofin.lab at *
            simp [hl, LE.le] at hlle; rw [hlle]; simp
            apply hind
            · exact Finset.erase_ssubset hx.1
            · rw [Finset.erase_inter, ← hst]
            · intro y hy z hz
              -- y ∈ s and y ≠ x, since y < z, and x ∈ next a s, then x ≠ z
              -- so z ∈ s since s is up closed
              sorry
            · intro y hy hyb
              refine Finset.mem_erase.2 ⟨?_, ?_⟩
              · intro hc; rw [hc, hl] at hyb; contradiction
              · exact hbot _ hy hyb
        | Label.lab_act ac =>
            have hlx := hle.lab x; unfold Lpofin.lab at *; rw [hl] at hlx
            rcases lab_is_act_le hlx with ⟨a', hbx, hxle⟩; rw [hbx]
            refine Linearizable.bind_mono (Sem.sem_mono (c := act) st hxle) ?_
            apply hind
            · exact Finset.erase_ssubset hx.1
            · rw [Finset.erase_inter, ← hst]
            -- Todo: move these goals to a common lemma
            · sorry --intro y hy; exact hs _ (Finset.erase_subset _ _ hy)
            · sorry
        | Label.lab_test bb =>
            have hlx := hle.lab x; unfold Lpofin.lab at *; rw [hl] at hlx
            rcases lab_is_test_le hlx with ⟨b', hbx, hxle⟩; rw [hbx]
            refine Linearizable.bind_mono (Sem.sem_mono (c := test) st hxle) ?_
            -- Need to prove that a.form = b.form
            sorry
  }

theorem lin_mono {m : Type → Type} {α act test : Type}
  [Monad m] [Sem act α (m α)] [Sem test α (m Bool)] [∀ β, PartialOrder (m β)]
  [∀ β, OrderBot (m β)] [Linearizable m] :
  Monotone (lin : Lpofin (Label act test) → α → m α) := by {
    unfold lin; intro α β hle
    refine lin_rec_mono ?_ ?_ ?_ hle
    · unfold Lpofin.nodes_finset; refine Eq.symm (Finset.inter_eq_right.2 ?_)
      simp [hle.nodes]
    · intro _ _ y hr; simp [Lpofin.nodes, Lpo.nodes]
      exact (Set.Finite.mem_toFinset _).mpr (α.val.property.rel_dom hr).2
    · intro _ hx _; exact (Set.Finite.mem_toFinset _).mpr hx
  }

lemma lin_rec_iso {m : Type → Type} {α act test : Type}
    [Monad m] [Sem act α (m α)] [Sem test α (m Bool)] [∀ β, Preorder (m β)]
    [OrderBot (m α)] [Linearizable m]
    {a : Lpofin (Label act test)} {e : Equiv.Perm Node} {s : Finset Node} :
    (lin_rec a s : α →  m α) = lin_rec (a.permute e) (s.image e) := by
  induction s using Finset.strongInduction with
  | H s hind =>
    ext st; unfold lin_rec; by_cases h : s = ∅
    · subst h; simp
    · simp only [h, ↓reduceIte, Finset.image_eq_empty]
      sorry

lemma lin_iso {m : Type → Type} {α act test : Type}
    [Monad m] [Sem act α (m α)] [Sem test α (m Bool)] [∀ β, Preorder (m β)]
    [OrderBot (m α)] [Linearizable m]
    {a b : Lpofin (Label act test)} (h : a ≈ b) :
    (lin a : α →  m α) = lin b := by
  unfold lin; rcases h with ⟨e, h⟩
  refine Eq.trans lin_rec_iso (congr_arg₂ _ (Subtype.ext h) ?_)
  have hn := congr_arg Lpo.nodes h; simp [permute, Lpo.nodes] at hn
  have _ : Fintype ↑(e '' a.val.val.nodes) := by
    unfold Lpo.nodes; rw [hn]; exact b.property.fintype
  have _ : Fintype ↑(b.val.val.nodes) := b.property.fintype
  refine (Set.Finite.toFinset_image _ _ ?_).symm.trans ?_
  · unfold Lpo.nodes; rw [hn]; exact b.property
  · unfold Lpofin.nodes_finset; unfold Set.Finite.toFinset
    refine @Set.toFinset_congr _ _ _ ?_ ?_ hn

end Lpo
