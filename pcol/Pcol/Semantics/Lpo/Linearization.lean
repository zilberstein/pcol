import Mathlib
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order

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

class Linearizable (t : Type → Type) (α : Type)
  [Monad t] [∀ {β : Type}, Preorder (t β)]
  where
  nondet {β : Type} : (s : Set β) → (↑s → t α) → t α
  nondet_mono {β : Type} {s : Set β} : Monotone (nondet s)
  -- nondet_mono {β : Type} {s u : Set β} {f : ↑s → t α} {g : ↑u → t α }
  --   (heq : s = u)
  --   (hle : ∀ x : ↑s, f x ≤ g (cast (congrArg Subtype heq) x)) :
  --   nondet s f ≤ nondet u g
  bind_mono {β γ : Type} : ∀ {m₁ m₂ : t β} {k₁ k₂ : β → t γ},
    m₁ ≤ m₂ → k₁ ≤ k₂ → bind m₁ k₁ ≤ bind m₂ k₂
 --  bind_additivity : ∀ f s, bind (nondet s) f = nondet (Finset.image (fun x => bind x f) s)

class Sem (c : Type) (in_type out_type : Type)
  extends Preorder c
  where
    sem : c → in_type → out_type
    sem_mono [Preorder out_type] (s : in_type) : Monotone (sem · s)

namespace Lpo

def Lpofin (l : Type) [Bot l] := { a : Lpo l // a.nodes.Finite }

instance {l : Type} [LE l] [Bot l] : LE (Lpofin l) where
  le a b := LE.le a.val b.val
instance {l : Type} [Preorder l] [Bot l] : Preorder (Lpofin l) :=
  Preorder.lift Subtype.val
instance {l : Type} [PartialOrder l] [Bot l] : PartialOrder (Lpofin l) :=
  PartialOrder.lift Subtype.val Subtype.val_injective

namespace Lpofin

noncomputable def nodes {l : Type} [Bot l] (a : Lpofin l) := a.property.toFinset
def rel {l : Type} [Bot l] (a : Lpofin l) := a.val.rel
def lab {l : Type} [Bot l] (a : Lpofin l) := a.val.lab
def form {l : Type} [Bot l] (a : Lpofin l) := a.val.form

end Lpofin

def next {l : Type} [Bot l] (a : Lpofin l) (s : Finset Node) : Set Node :=
  { x | x ∈ s ∧ ∀ y, a.rel y x → y ∉ s }

def remaining {l : Type} [Bot l] (a : Lpofin l) (φ : Form Node) (s : Set Node) :
  Set (Subtype (fun x => x ∈ s)) :=
  { x | Form.sat (Form.and φ (a.1.form x.1)) }

-- lemma next_sub_s {l : Type} [Bot l] {a : Lpo l} {s : Finset Node} :
--   ∀ x, x ∈ next a s → x.val ∈ s := by sorry

def lin_rec {t : Type → Type} {α act test: Type}
  [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
  [Linearizable t α] [Bot (t α)]
  (a : Lpofin (Label act test)) (s : Finset Node) (st : α) : t α :=
  if s = ∅ then
    pure st
  else
    Linearizable.nondet (next a s) fun x =>
      have _h : (s.erase x.val).card < s.card := Finset.card_erase_lt_of_mem x.property.1
      match a.lab x with
      | Label.lab_bot => ⊥
      | Label.lab_fork => lin_rec a (s.erase x.1) st
      | Label.lab_act ac => bind (Sem.sem ac st) (lin_rec a (s.erase x.1))
      | Label.lab_test b =>
          bind (Sem.sem b st)
            fun (r : Bool) =>
              let φ : Form Node := cond r (Form.literal x.val) (Form.literal x.val).not
              lin_rec a ((s.erase x.val).filter fun z => (φ.and (a.form z)).sat) st
termination_by s.card
decreasing_by
· exact _h
· exact _h
· exact lt_of_lt_of_le' _h (Finset.card_filter_le _ _)

noncomputable def lin {t : Type → Type} {α act test: Type}
  [Sem act α (t α)] [Sem test α (t Bool)] [Monad t] [∀ {β : Type}, Preorder (t β)]
  [Linearizable t α] [Bot (t α)]
  (a : Lpofin (Label act test)) : α → t α :=
    lin_rec a a.nodes

lemma next_iso {l : Type} [Bot l] [LE l] {s t : Finset Node} {a b : Lpofin l}
  (hle : a ≤ b)
  (hst : s = t ∩ a.nodes)
  (hscl : a.rel.IsUpClosed s)
  (hbot : ∀ x ∈ a.nodes, a.lab x = ⊥ → x ∈ s) :
  next a s = next b t := by {
    have hsub : s ⊆ t := by rw [hst]; exact Finset.inter_subset_left
    have ha : s ⊆ a.nodes := by rw [hst]; exact Finset.inter_subset_right
    unfold Lpofin.nodes at *
    unfold next; ext x; simp; constructor
    · intro ⟨hx, hr⟩; refine ⟨hsub hx, fun y hy hc => ?_⟩
      have hxa := (Set.Finite.mem_toFinset _).1 (ha hx)
      have hya := hle.downcl _ hxa y hy
      unfold Lpofin.rel at hy
      rw [← hle.rel _ hya _ hxa] at hy
      have hys : y ∈ s := by {
        rw [hst]
        exact Finset.mem_inter.2 ⟨hc, (Set.Finite.mem_toFinset a.property).2 hya⟩
      }
      exact hr y hy hys
    · intro ⟨hx, hr⟩; refine ⟨?_, fun y hy hc => ?_,⟩
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
  [OrderBot (m α)] [Linearizable m α]
  {s t : Finset Node} {a b : Lpofin (Label act test)}
  (hst : s = t ∩ a.nodes)
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
        -- Need that s = ∅ ↔ t = ∅
        sorry
      · have ht : t ≠ ∅ := by sorry
        simp [eq_false h, eq_false ht];
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
            refine Linearizable.bind_mono (α := α) (Sem.sem_mono (c := act) st hxle) ?_
            apply hind
            · exact Finset.erase_ssubset hx.1
            · rw [Finset.erase_inter, ← hst]
            -- Todo: move these goals to a common lemma
            · sorry --intro y hy; exact hs _ (Finset.erase_subset _ _ hy)
            · sorry
        | Label.lab_test bb =>
            have hlx := hle.lab x; unfold Lpofin.lab at *; rw [hl] at hlx
            rcases lab_is_test_le hlx with ⟨b', hbx, hxle⟩; rw [hbx]
            refine Linearizable.bind_mono (α := α) (Sem.sem_mono (c := test) st hxle) ?_
            -- Need to prove that a.form = b.form
            sorry
  }

theorem lin_mono {m : Type → Type} {α act test : Type}
  [Monad m] [Sem act α (m α)] [Sem test α (m Bool)] [∀ β, Preorder (m β)]
  [OrderBot (m α)] [Linearizable m α] :
  Monotone (lin : Lpofin (Label act test) → α → m α) := by {
    unfold lin; intro α β hle
    refine lin_rec_mono ?_ ?_ (fun _ hx _ => hx) hle
    · unfold Lpofin.nodes; refine Eq.symm (Finset.inter_eq_right.2 ?_)
      simp [hle.nodes]
    · intro _ _ y hr; simp [Lpofin.nodes, Lpo.nodes]
      exact (α.val.property.rel_dom hr).2
  }

end Lpo
