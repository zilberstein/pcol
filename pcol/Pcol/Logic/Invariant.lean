import Pcol.Logic.Mem
import Pcol.Semantics.Lpo.Linearization

open Classical

-- Invariant Sensitive Semantics

-- Add an invariant to an action
structure WithInv (act : Type) (u : Finset Var) where
  action : act
  inv_dom : Finset Var
  inv_dom_valid : inv_dom ⊆ u
  inv : Finset (Mem inv_dom)

namespace WithInv

def upcast {act : Type} {u v : Finset Var} (a : WithInv act u) (h : u ⊆ v) : WithInv act v := {
  action := a.action
  inv_dom := a.inv_dom
  inv_dom_valid := a.inv_dom_valid.trans h
  inv := a.inv
}

def has_inv {act : Type} {u v : Finset Var}
    (a : WithInv act u) (inv : Finset (Mem v)) : Prop :=
  ∃ h : v = a.inv_dom, by { rw [h] at inv; exact a.inv = inv }

end WithInv

namespace Lpofin

def has_inv {act test : Type} {u v : Finset Var}
    (α : Lpofin (Label (WithInv act u) (WithInv test u)))
    (inv : Finset (Mem v)) : Prop :=
  ∀ x ∈ α.nodes,
    match α.lab x with
    | Label.lab_bot => True
    | Label.lab_fork => True
    | Label.lab_act a => a.has_inv inv
    | Label.lab_test t => t.has_inv inv

end Lpofin

def upcast_lab {act test : Type} {u v : Finset Var}
    (l : Label (WithInv act u) (WithInv test u))
    (h : u ⊆ v) :
    Label (WithInv act v) (WithInv test v) :=
  match l with
  | Label.lab_bot => Label.lab_bot
  | Label.lab_fork => Label.lab_fork
  | Label.lab_act a => Label.lab_act (a.upcast h)
  | Label.lab_test a => Label.lab_test (a.upcast h)

namespace Lpofin

def upcast {act test : Type}  {u v : Finset Var}
    (α : Lpofin (Label (WithInv act u) (WithInv test u))) (h : u ⊆ v) :
    Lpofin (Label (WithInv act v) (WithInv test v)) := {
  val := {
    val := {
      nodes := α.nodes
      rel := α.rel
      lab x := upcast_lab (α.lab x) h
      form := α.form
    }
    property := by
      constructor
      · exact α.val.property.rel_dom
      · simp only [Lpofin.lab]; intro _ hx
        exact (congrArg₂ _ (α.val.property.lab_dom _ hx) rfl)
      · exact α.val.property.rel
      · simp only [Lpofin.lab]; intro x hx; sorry
      · exact α.val.property.form_dom
      · exact α.val.property.form
  }
  property := α.property
}

end Lpofin

instance {act : Type} {u : Finset Var} : LE (WithInv act u) where
  le a₁ a₂ :=
    a₁.action = a₂.action ∧
    ∃ hsub : a₂.inv_dom ⊆ a₁.inv_dom,
    ∃ inv : Finset (Mem (a₁.inv_dom \ a₂.inv_dom)),
      a₁.inv = sorry
      --Mem.sep a₂.inv inv Finset.disjoint_sdiff (Finset.union_sdiff_of_subset hsub)

instance {act : Type} {u : Finset Var} : Preorder (WithInv act u) where
  le_refl := by {
    intro a; refine ⟨rfl, Finset.Subset.refl _, cast ?_ ({Mem.emp} : Finset (Mem ∅)), ?_⟩
    · refine congrArg _ (congrArg _ ?_); exact (Finset.sdiff_self _).symm
    · sorry
  }
  le_trans := sorry

instance {act : Type} {u : Finset Var} : PartialOrder (WithInv act u) where
  le_antisymm := sorry

namespace Inv

noncomputable def check {t : Type → Type} [Monad t] [∀ X, Bot (t X)] {u v : Finset Var}
    (inv : Finset (Mem v)) (σ : Mem u) (h : v ⊆ u) : t (Mem u) :=
  if σ.proj h ∈ inv then pure σ else ⊥

def replace {t : Type → Type} [Monad t]
    [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t] {u v : Finset Var}
    (inv : Finset (Mem v)) (σ : Mem u) : t (Mem u) :=
  Linearizable.nondet fun τ : ↑inv ↦ pure fun x ↦
    if hx : x.val ∈ v then τ.val ⟨x.val, hx⟩ else σ x

end Inv

-- The semantics of WithInv first checks the invariant, then
-- nondeterministically selects a
noncomputable instance {t : Type → Type} [Monad t] {act : Type} {u : Finset Var}
  [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t]
  [Sem act (Mem u) (t (Mem u))] :
  Sem (WithInv act u) (Mem u) (t (Mem u)) where
  sem a σ := do
    let σ₁ ← Inv.check a.inv σ a.inv_dom_valid
    let σ₂ ← Inv.replace a.inv σ₁
    let τ ← Sem.sem a.action σ₂
    Inv.check a.inv τ a.inv_dom_valid
  sem_mono := sorry

noncomputable instance {t : Type → Type} [Monad t] {test : Type} {u : Finset Var}
  [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t] [Sem test (Mem u) Bool] :
  Sem (WithInv test u) (Mem u) (t Bool) where
  sem t σ := do
    let σ₁ ← Inv.check t.inv σ t.inv_dom_valid
    let σ₂ ← Inv.replace t.inv σ₁
    pure (Sem.sem t.action σ₂)
  sem_mono := sorry

lemma inv_sem_eq {t : Type → Type} [Monad t] {act : Type} {u v : Finset Var}
    [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t]
    [Sem act (Mem u) (t (Mem u))]
    {inv : Finset (Mem v)}
    {a : WithInv act u} (hinv : a.has_inv inv)
    {σ : Mem (u \ v)} {τ₁ τ₂ : Mem v} (hτ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv) :
    (Sem.sem a (σ.union τ₁ ⟨Finset.sdiff_disjoint, (sorry : u = (u \ v) ∪ v)⟩) : t (Mem u)) =
    (Sem.sem a (σ.union τ₂ ⟨Finset.sdiff_disjoint, (sorry : u = (u \ v) ∪ v)⟩) : t (Mem u)) := by
  --refine congrArg₂ bind ?_ rfl
  sorry

lemma inv_sem_eq_test {t : Type → Type} [Monad t] {test : Type} {u v : Finset Var}
    [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t]
    [Sem test (Mem u) Bool]
    {inv : Finset (Mem v)}
    {a : WithInv test u} (hinv : a.has_inv inv)
    {σ : Mem (u \ v)} {τ₁ τ₂ : Mem v} (hτ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv) :
    (Sem.sem a (σ.union τ₁ ⟨Finset.sdiff_disjoint, (sorry : u = (u \ v) ∪ v)⟩) : t Bool) =
    (Sem.sem a (σ.union τ₂ ⟨Finset.sdiff_disjoint, (sorry : u = (u \ v) ∪ v)⟩) : t Bool) := by
  sorry

-- This would have to be proved by cases on the type of action
-- Intuitively it's true because when you upcast an action, it means that the domain
-- includes more variables. Those variables are either not used (in which case the
-- behavior doesn't change), or they are used and then the prior behavior is ⊥
lemma upcast_mono {t : Type → Type} [Monad t] {act : Type} {u₁ u₂ u : Finset Var}
    [∀ X, Preorder (t X)] [∀ X, Bot (t X)] [Linearizable t]
    [∀ v, Sem act (Mem v) (t (Mem v))]
    {a : WithInv act u₁} (h : Disjoint u₂ u₁ ∧ u = u₂ ∪ u₁)
    {σ₁ : Mem u₁} {σ₂ : Mem u₂} :
    (bind (Sem.sem a σ₁ : t (Mem u₁)) (fun σ₁' : Mem u₁ ↦ pure (σ₂.union σ₁' h))) ≤
    (Sem.sem (a.upcast (sorry : u₁ ⊆ u)) (σ₂.union σ₁ h) : t (Mem u)) := sorry

lemma upcast_mono_test {m : Type → Type} [Monad m] {test : Type} {u₁ u₂ u : Finset Var}
    [∀ X, Preorder (m X)] [∀ X, Bot (m X)] [Linearizable m]
    [∀ v, Sem test (Mem v) Bool]
    {t : WithInv test u₁} (h : Disjoint u₂ u₁ ∧ u = u₂ ∪ u₁)
    {σ₁ : Mem u₁} {σ₂ : Mem u₂} :
    (Sem.sem t σ₁ : m Bool) ≤
    (Sem.sem (t.upcast (sorry : u₁ ⊆ u)) (σ₂.union σ₁ h) : m Bool) := sorry
