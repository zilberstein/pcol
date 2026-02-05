import Init.Prelude
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.ENNReal.Basic

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

class Lin (t : Type → Type) extends Monad t where
  -- Nondeterministic choice with minimum probability `p` for
  -- first choice (so that nondet_min 1 m₁ m₂ = m₁)
  nondet_min {α : Type} : ENNReal → t α → t α → t α

  -- Nondeterministic choice
  nondet {ι α : Type} : (ι → t α) → t α

export Lin (nondet_min nondet)

class LawfulLin (t : Type → Type) [Lin t] where

  nondet_min_mono {α : Type} [Preorder (t α)] : ∀ {m₁ m₂ t₁ t₂ : t α} (p : ENNReal),
    m₁ ≤ m₂ → t₁ ≤ t₂ → Lin.nondet_min p m₁ t₁ ≤ Lin.nondet_min p m₂ t₂

  nondet_mono {ι α : Type} [Preorder (t α)] : Monotone (Lin.nondet : (ι → t α) → t α)

  pure_mono {α : Type} [Preorder α] [Preorder (t α)] : ∀ {a₁ a₂ : α},
    a₁ ≤ a₂ → (pure a₁ : t α) ≤ pure a₂

  bind_mono_left {β γ : Type} [Preorder (t β)] [Preorder (t γ)] : ∀ {m₁ m₂ : t β} {k : β → t γ},
    m₁ ≤ m₂ /-→ k₁ ≤ k₂-/ → bind m₁ k ≤ bind m₂ k
 --  bind_additivity : ∀ f s, bind (nondet s) f = nondet (Finset.image (fun x => bind x f) s)

  bind_mono_right {β γ : Type} [Preorder (t β)] [Preorder (t γ)] : ∀ {m : t β} {k₁ k₂ : β → t γ},
    k₁ ≤ k₂ /-→ k₁ ≤ k₂-/ → bind m k₁ ≤ bind m k₂

class Sem (α σ τ : Type) where
  sem : α → σ → τ

export Sem (sem)

class LawfulSem (α σ τ : Type)
  [Preorder α] [Preorder τ] [Sem α σ τ]
where
  sem_mono (s : σ) : Monotone (sem · s : α → τ)

abbrev Invariant (δ : Type → Type) (σ : Type) := δ σ × Finset σ

-- Compatible projection
class CompatibleProj (α β : Type) where
  cprojr : α → β → α
  cprojl b a := cprojr a b

notation:65 a " ◃ " b => CompatibleProj.cprojr a b
notation:65 b " ▹ " a => CompatibleProj.cprojl b a

class Check (t δ : Type → Type) (σ : Type) where
  check : Invariant δ σ → σ → t σ

export Check (check)

class LawfulCheck (t δ : Type → Type) (σ : Type)
  [Preorder σ] [Preorder (t σ)] [Check t δ σ]
where
  check_mono (inv : Invariant δ σ) : Monotone (check inv : σ → t σ)

class Replace (t δ : Type → Type) (σ : Type) where
  replace : σ → Invariant δ σ → t σ

export Replace (replace)

class LawfulReplace (t δ : Type → Type) (σ : Type)
  [Preorder σ] [Preorder (t σ)] [Replace t δ σ]
where
  replace_mono (inv : Invariant δ σ) : Monotone (replace · inv : σ → t σ)

class InvSem (δ : Type → Type) (α σ τ : Type) where
  inv_sem : α → Invariant δ σ → σ → τ

export InvSem (inv_sem)

class LawfulInvSem (δ : Type → Type) (α σ τ : Type)
  [Preorder α] [Preorder τ] [InvSem δ α σ τ]
where
  inv_sem_mono (s : σ) (inv : Invariant δ σ) : Monotone (inv_sem · inv s : α → τ)

instance {α σ : Type} {t δ : Type → Type}
  [Check t δ σ] [Replace t δ σ] [Lin t] : [Sem α σ (t σ)] → InvSem δ α σ (t σ)
where
  inv_sem a inv s := do
    let s' ← Check.check inv s
    let s'' ← Replace.replace s' inv
    let s''' ← Sem.sem a s''
    Check.check inv s'''

instance {t δ : Type → Type} {α σ : Type}
  [Preorder α] [Preorder σ] [∀ {β}, Preorder (t β)]
  [Check t δ σ] [Replace t δ σ] [Lin t] [Sem α σ (t σ)]
  [LawfulCheck t δ σ] [LawfulReplace t δ σ] [LawfulLin t]
  : [LawfulSem α σ (t σ)] → LawfulInvSem δ α σ (t σ)
where
  inv_sem_mono s inv := by
    intros a₁ a₂ hle
    simp [inv_sem]
    apply LawfulLin.bind_mono_right
    refine Pi.le_def.2 ?_ ; intros
    apply LawfulLin.bind_mono_right
    refine Pi.le_def.2 ?_ ; intros
    apply LawfulLin.bind_mono_left
    apply LawfulSem.sem_mono
    assumption


instance {α σ τ : Type} {t δ : Type → Type}
  [Check t δ σ] [Replace t δ σ] [Lin t] : [Sem α σ τ] → InvSem δ α σ (t τ)
where
  inv_sem a inv s := do
    let s' ← Check.check inv s
    let s'' ← Replace.replace s' inv
    pure (Sem.sem a s'')

instance {t δ : Type → Type} {α σ τ : Type}
  [Preorder α] [Preorder σ] [Preorder τ] [∀ {β}, Preorder (t β)]
  [Check t δ σ] [Replace t δ σ] [Lin t] [Sem α σ τ]
  [LawfulCheck t δ σ] [LawfulReplace t δ σ] [LawfulLin t]
  : [LawfulSem α σ τ] → LawfulInvSem δ α σ (t τ)
where
  inv_sem_mono s inv := by
    intros a₁ a₂ hle
    simp [inv_sem]
    apply LawfulLin.bind_mono_right
    refine Pi.le_def.2 ?_ ; intros
    apply LawfulLin.bind_mono_right
    refine Pi.le_def.2 ?_ ; intros
    apply LawfulLin.pure_mono
    apply LawfulSem.sem_mono
    assumption
