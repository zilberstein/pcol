import Mathlib.Data.Finset.Lattice.Basic

import Pcol.ConvexPowerset
import Pcol.ConvexPowerset.Monad

import Pcol.Semantics.Lpo.Linearization
import Pcol.Semantics.Lpo.Operations.Par

open Classical

-- Some preliminary stuff that really belongs elsewhere

def Var := Nat
instance : DecidableEq Var := instDecidableEqNat

def Val := Nat
def Mem (v : Finset Var) := ↑v → Val

@[ext]
theorem mem_ext {u : Finset Var} {σ τ : Mem u} (h : ∀ x, σ x = τ x) : σ = τ := funext h

namespace Mem

noncomputable def union {u u₁ u₂ : Finset Var} (σ : Mem u₁) (τ : Mem u₂)
  (hu : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) : Mem u :=
  fun x ↦
    if h : x.val ∈ u₁ then
      σ ⟨x.val, h⟩
    else
      τ ⟨x.val, by
        obtain ⟨x, hx⟩ := x; rw [hu.2] at hx
        rcases Finset.mem_union.mp hx with hx | hx
        · exfalso; exact h hx
        · exact hx
      ⟩
def emp : Mem ∅ := fun x ↦ False.elim (Finset.not_mem_empty _ x.property)

def castMem {u v : Finset Var} (σ : Mem u) (h : u = v) : Mem v :=
  cast (congrArg _ h) σ

noncomputable def sep {u u₁ u₂ : Finset Var} (A : Set (Mem u₁)) (B : Set (Mem u₂))
    (hu : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) :
    Set (Mem u) :=
  ⋃ σ ∈ A, ⋃ τ ∈ B, { σ.union τ hu }

lemma sep_emp {u : Finset Var} (σ : Mem u) :
    σ.union emp ⟨Finset.disjoint_empty_right _, (Finset.union_empty _).symm⟩ = σ := by sorry

def proj {u v : Finset Var} (σ : Mem u) (h : v ⊆ u) : Mem v :=
  fun x ↦ σ ⟨x.val, h x.property⟩

lemma union_mem {u u₁ u₂ : Finset Var} {σ : Mem u₁} {τ : Mem u₂} {A : Set (Mem u₁)} {B : Set (Mem u₂)}
    (h : Disjoint u₁ u₂ ∧ u = u₁ ∪ u₂) :
    σ.union τ h ∈ Mem.sep A B h ↔ σ ∈ A ∧ τ ∈ B := by
  sorry

end Mem

noncomputable def prob {α : Type} (μ : Distr α) (A : Set α) : ENNReal :=
  ∑' x : ↑A, μ x

noncomputable def minProb {α : Type} (S : C α) (A : Set α) : ENNReal :=
  ⨅ μ ∈ S, prob μ A

lemma minProb_bind {X Y : Type} (S : C X) (f : X → C Y) (A : Set Y) :
    minProb (bind S f) A =
    ⨅ μ ∈ S, ∑' x : ↑{ x : X | some x ∈ μ.support }, μ x * minProb (f x) A := sorry

lemma minProb_pure {X : Type} (x : X) (A : Set X) :
    minProb (pure x) A = if x ∈ A then 1 else 0 := by
  refine iInf_singleton.trans ?_; sorry

lemma minProb_bot {X : Type} {A : Set X} :
    minProb ⊥ A = 0 := by
  refine eq_bot_iff.mpr ?_
  have h : ⊥ = prob ⊥ A := by sorry
  rw [h]; refine biInf_le _ ?_; exact Set.mem_univ _

lemma minProb_ne_top {X : Type} {s : C X} {A : Set X} :
    minProb s A ≠ ⊤ := by
  sorry

lemma iInf_next_mul {l X : Type} [Bot l] {α : Lpofin l} {s : Finset Node} {t : C X} {A : Set X}
    {f : ↑(Lpo.next α s) → ENNReal} (h : s ≠ ∅) :
    iInf f * minProb t A = iInf fun x ↦ f x * minProb t A := by
  refine @ENNReal.iInf_mul _ _ _ ?_ ?_
  · sorry -- This is a bit tricky since we have to find the minimal element
  · intro c; exfalso; exact minProb_ne_top c

lemma mul_iInf_next {l X : Type} [Bot l] {α : Lpofin l} {s : Finset Node} {t : C X} {A : Set X}
    {f : ↑(Lpo.next α s) → ENNReal} (h : s ≠ ∅) :
    minProb t A * iInf f = iInf fun x ↦ minProb t A * f x :=
  (mul_comm _ _).trans ((iInf_next_mul h).trans
    (iInf_congr fun _ ↦ mul_comm _ _))

instance {X : Type} : Linearizable C X where
  nondet {ι} (f : ι → C X) := bind ⟨(Set.univ : Set (Distr ι)), sorry⟩ f
  nondet_mono := sorry
  nondet_congr := by
    intro ι ι' f g e h; simp only
    sorry
  bind_mono := sorry

lemma nondet_singleton {u : Finset Var} {X : Type} {x : X} {f : ↑(Set.singleton x) → C (Mem u)} :
    Linearizable.nondet f = f ⟨x, Set.mem_singleton _⟩ := sorry

lemma minProb_nondet {u : Finset Var} {ι : Type} (f : ι → C (Mem u)) (A : Set (Mem u)) :
    minProb (Linearizable.nondet f) A =
    ⨅ x : ι, minProb (f x) A := sorry

structure WithInv (act : Type) (u : Finset Var) where
  action : act
  inv_dom : Finset Var
  inv_dom_valid : inv_dom ⊆ u
  inv : Finset (Mem inv_dom)

def upcast {act : Type} {u v : Finset Var} (a : WithInv act u) (h : u ⊆ v) : WithInv act v := {
  action := a.action
  inv_dom := a.inv_dom
  inv_dom_valid := a.inv_dom_valid.trans h
  inv := a.inv
}

def upcast_lab {act test : Type} {u v : Finset Var}
    (l : Label (WithInv act u) (WithInv test u))
    (h : u ⊆ v) :
    Label (WithInv act v) (WithInv test v) :=
  match l with
  | Label.lab_bot => Label.lab_bot
  | Label.lab_fork => Label.lab_fork
  | Label.lab_act a => Label.lab_act (upcast a h)
  | Label.lab_test a => Label.lab_test (upcast a h)

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

def check {u v : Finset Var} (inv : Finset (Mem v)) (σ : Mem u) (h : v ⊆ u) : C (Mem u) :=
  if σ.proj h ∈ inv then pure σ else ⊥

def replace {u v : Finset Var} (inv : Finset (Mem v)) (σ : Mem u) : C (Mem u) :=
  Linearizable.nondet fun τ : ↑inv ↦ pure fun x ↦
    if hx : x.val ∈ v then τ.val ⟨x.val, hx⟩ else σ x

end Inv

instance {act : Type} {u : Finset Var} [Sem act (Mem u) (C (Mem u))] :
  Sem (WithInv act u) (Mem u) (C (Mem u)) where
  sem a σ := do
    let σ₁ ← Inv.check a.inv σ a.inv_dom_valid
    let σ₂ ← Inv.replace a.inv σ₁
    let τ ← Sem.sem a.action σ₂
    Inv.check a.inv τ a.inv_dom_valid
  sem_mono := sorry

instance {test : Type} {u : Finset Var} [Sem test (Mem u) Bool] :
  Sem (WithInv test u) (Mem u) (C Bool) where
  sem t σ := do
    let σ₁ ← Inv.check t.inv σ t.inv_dom_valid
    let σ₂ ← Inv.replace t.inv σ₁
    pure (Sem.sem t.action σ₂)
  sem_mono := sorry

namespace Lpofin

def has_inv {act test : Type} {u v : Finset Var}
    (α : Lpofin (Label (WithInv act u) (WithInv test u)))
    (inv : Finset (Mem v)) : Prop :=
  ∀ x ∈ α.nodes,
    match α.lab x with
    | Label.lab_bot => True
    | Label.lab_fork => True
    | Label.lab_act a =>
      ∃ h : v = a.inv_dom, a.inv = cast (congrArg _ (congrArg _ h)) inv
    | Label.lab_test t =>
      ∃ h : v = t.inv_dom, t.inv = cast (congrArg _ (congrArg _ h)) inv

end Lpofin

def par_comp {u₁ u₂ u : Finset Var} {act test : Type}
    (α : Lpofin (Label (WithInv act u₁) (WithInv test u₁)))
    (β : Lpofin (Label (WithInv act u₂) (WithInv test u₂)))
    (hdn : Disjoint α.nodes β.nodes) (hu : u = u₁ ∪ u₂)
    {root : Node} (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes) :
    Lpofin (Label (WithInv act u) (WithInv test u)) := sorry

lemma par_comp_lab_root {u₁ u₂ u : Finset Var} {act test : Type}
    {α : Lpofin (Label (WithInv act u₁) (WithInv test u₁))}
    {β : Lpofin (Label (WithInv act u₂) (WithInv test u₂))}
    (hdn : Disjoint α.nodes β.nodes) (hu : u = u₁ ∪ u₂)
    {root : Node} (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes) :
    (par_comp α β hdn hu hr₁ hr₂).lab root = Label.lab_fork := sorry

lemma par_comp_comm {u₁ u₂ u : Finset Var} {act test : Type}
    {α : Lpofin (Label (WithInv act u₁) (WithInv test u₁))}
    {β : Lpofin (Label (WithInv act u₂) (WithInv test u₂))}
    {hdn : Disjoint α.nodes β.nodes} (hu : u = u₁ ∪ u₂)
    {root : Node} {hr₁ : root ∉ α.nodes} {hr₂ : root ∉ β.nodes} :
    par_comp α β hdn hu hr₁ hr₂ = par_comp β α hdn.symm (hu.trans (Finset.union_comm _ _)) hr₂ hr₁ := sorry

lemma next_par {u₁ u₂ u : Finset Var} {act test : Type}
    (α : Lpofin (Label (WithInv act u₁) (WithInv test u₁)))
    (β : Lpofin (Label (WithInv act u₂) (WithInv test u₂)))
    (hdn : Disjoint α.nodes β.nodes) (hu : u = u₁ ∪ u₂)
    {root : Node} (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes)
    (s : Finset Node) :
    Lpo.next (par_comp α β hdn hu hr₁ hr₂) s = {root} ∨
    (Lpo.next (par_comp α β hdn hu hr₁ hr₂) s = Lpo.next α (s ∩ α.nodes_finset) ∪ Lpo.next β (s ∩ β.nodes_finset) ∧
      s ∩ α.nodes_finset ≠ ∅ ∧ s ∩ β.nodes_finset ≠ ∅) ∨
    (Lpo.next (par_comp α β hdn hu hr₁ hr₂) s = Lpo.next α (s ∩ α.nodes_finset) ∧
      s ∩ α.nodes_finset ≠ ∅) ∨
    (Lpo.next (par_comp α β hdn hu hr₁ hr₂) s = Lpo.next β (s ∩ β.nodes_finset) ∧
      s ∩ β.nodes_finset ≠ ∅)
    := sorry

lemma dsj₁ {u₁ u₂ v : Finset Var} (h : v = u₁ ∩ u₂) :
    Disjoint (u₁ \ v) v ∧ u₁ = (u₁ \ v) ∪ v := by
  refine ⟨Finset.sdiff_disjoint, (Finset.sdiff_union_of_subset ?_).symm⟩
  rw [h]; exact Finset.inter_subset_left

lemma dsj₂ {u₁ u₂ v : Finset Var} (h : v = u₁ ∩ u₂) :
    Disjoint (u₂ \ v) v ∧ u₂ = (u₂ \ v) ∪ v :=
  dsj₁ (h.trans (Finset.inter_comm _ _))

lemma dsj₁₂ {u₁ u₂ u v : Finset Var} (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    Disjoint (u₁ \ v) u₂ ∧ u = (u₁ \ v) ∪ u₂ := by
  rw [hv, Finset.sdiff_inter_self_left]; constructor
  · exact Finset.sdiff_disjoint
  · exact hu.trans Finset.sdiff_union_self_eq_union.symm

lemma dsj₂₁ {u₁ u₂ u v : Finset Var} (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    Disjoint (u₂ \ v) u₁ ∧ u = (u₂ \ v) ∪ u₁ :=
  dsj₁₂ (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _))

lemma union_comm_assoc {u u₁ u₂ v : Finset Var}
    {σ₁ : Mem (u₁ \ v)} {σ₂ : Mem (u₂ \ v)} {τ : Mem v}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)) =
    (σ₂.union (σ₁.union τ (dsj₁ hv)) (dsj₂₁ hu hv)) := by
  ext ⟨x, hx⟩; unfold Mem.union; by_cases hx' : x ∈ u₁ \ v
  · simp only [hx', ↓reduceDIte, Finset.mem_sdiff]; sorry
  · sorry

lemma sep_comm_assoc {u u₁ u₂ v : Finset Var}
    {A : Set (Mem (u₁ \ v))} {B : Set (Mem (u₂ \ v))} {I : Set (Mem v)}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    (Mem.sep A (Mem.sep B I (dsj₂ hv)) (dsj₁₂ hu hv)) =
    (Mem.sep B (Mem.sep A I (dsj₁ hv)) (dsj₂₁ hu hv)) := by sorry

noncomputable def equiv_sem_upcast {act : Type} {u u₁ u₂ v : Finset Var}
    [∀ u, Sem act (Mem u) (C (Mem u))] {a : WithInv act u₁}
    {σ₁ : Mem (u₁ \ v)} {σ₂ : Mem (u₂ \ v)} {τ τ₁ : Mem v}
    (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂) :
    Subtype (Membership.mem
      (@Sem.sem (WithInv act u) (Mem u) (C (Mem u)) _
        (upcast a (by { rw [hu]; exact Finset.subset_union_left }))
        (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))) ≃
    Subtype (Membership.mem
      (@Sem.sem (WithInv act u₁) (Mem u₁) (C (Mem u₁)) _ a (σ₁.union τ₁ (dsj₁ hv)))) := {
  toFun := by
    intro ⟨μ, hμ⟩
    refine
      ⟨PMF.bind μ fun σ ↦ pure
        (match σ with
         | ⊥ => ⊥
         | some σ => some (σ.proj ?_)), ?_⟩
    · rw [hu]; exact Finset.subset_union_left
    · sorry
  invFun := by
    intro ⟨μ, hμ⟩
    refine
      ⟨PMF.bind μ fun σ ↦ pure
        (match σ with
         | ⊥ => ⊥
         | some σ => some (σ₂.union σ (dsj₂₁ hu hv))), ?_⟩
    sorry
  left_inv := by
    intro ⟨μ, hμ⟩
    simp only [id_eq, eq_mpr_eq_cast, PMF.bind_bind, Subtype.mk.injEq]
    sorry
  right_inv := sorry
 }

-- lemma tsum_upcast {u u₁ u₂ v : Finset Var} {act : Type}
--     [∀ u, Sem (WithInv act u) (Mem u) (C (Mem u))]
--     (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂)
--     {μ : Distr (Mem u) } {a : WithInv act u₁}
--     {σ₁ : Mem (u₁ \ v)} {σ₂ : Mem (u₂ \ v)} {τ : Mem v}
--     (hμ : μ ∈ Sem.sem (upcast a sorry) (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
--     {f : ↑{x | some x ∈ PMF.support ((equiv_sem_upcast hu hv) ⟨μ, hμ⟩).val } → ENNReal } :
--     ∑' x : ↑{x | some x ∈ PMF.support ((equiv_sem_upcast hu hv) ⟨μ, hμ⟩).val}, f x =
--     ∑' x : ↑{ x | some x ∈ PMF.support μ }, f (equiv_sem_upcast hu hv x) := by

lemma tsum_congr' {ι ι' : Type} {f : ι → ENNReal} {g : ι' → ENNReal}
    (e : ι ≃ ι') (h : ∀ x, f x = g (e x)) :
    ∑' x, f x = ∑' x, g x := by
  refine Eq.symm (ENNReal.summable.hasSum_iff.mp ?_)
  refine (e.hasSum_iff  (α := ENNReal)).mp ?_
  have : g ∘ e = f := by
    ext x; exact (h x).symm
  rw [this]
  exact ENNReal.summable.hasSum

variable {u u₁ u₂ v : Finset Var} {act test : Type}
  [∀ u, Sem act (Mem u) (C (Mem u))]
  [∀ u, Sem test (Mem u) Bool]
  {α : Lpofin (Label (WithInv act u₁) (WithInv test u₁))}
  {β : Lpofin (Label (WithInv act u₂) (WithInv test u₂))}
  {root : Node} (hr₁ : root ∉ α.nodes) (hr₂ : root ∉ β.nodes)
  {inv : Finset (Mem v)} (hinv₁ : α.has_inv inv) (hinv₂ : β.has_inv inv)
  (hu : u = u₁ ∪ u₂) (hv : v = u₁ ∩ u₂)
  (hdn : Disjoint α.nodes β.nodes)
  (A : Set (Mem (u₁ \ v))) (B : Set (Mem (u₂ \ v)))

def is_indep
  (s : Finset Node) (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv) : Prop :=
  minProb (Lpo.lin_rec (par_comp α β hdn hu hr₁ hr₂) s (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv) : Set (Mem u)) =
  minProb (Lpo.lin_rec α (s ∩ α.nodes_finset) (σ₁.union τ₁ (dsj₁ hv) : Mem u₁)) (Mem.sep A ↑inv (dsj₁ hv)) *
    minProb (Lpo.lin_rec β (s ∩ β.nodes_finset) (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv))

lemma flip_hind
    {s : Finset Node}
    (hind : ∀ t ⊂ s,
      ∀ (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv),
      is_indep hr₁ hr₂ hu hv hdn A B t σ₁ σ₂ hτ hτ₁ hτ₂) :
    ∀ t ⊂ s,
    ∀ {σ₂ : Mem (u₂ \ v)} {σ₁ : Mem (u₁ \ v)} {τ τ₂ τ₁ : Mem v}
      (hτ : τ ∈ inv) (hτ₂ : τ₂ ∈ inv) (hτ₁ : τ₁ ∈ inv),
      is_indep hr₂ hr₁
        (hu.trans (Finset.union_comm _ _))
        (hv.trans (Finset.inter_comm _ _)) hdn.symm B A t σ₂ σ₁ hτ hτ₂ hτ₁ := by
  intro t ht σ₁ σ₂ τ τ₁ τ₂ hτ hτ₁ hτ₂; unfold is_indep
  rw [par_comp_comm,
      union_comm_assoc (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _)),
      sep_comm_assoc (hu.trans (Finset.union_comm _ _)) (hv.trans (Finset.inter_comm _ _)),
      mul_comm]
  exact hind t ht σ₂ σ₁ hτ hτ₂ hτ₁

 lemma par_comp_inductive_step
    {s : Finset Node} {x : Node} (hx : x ∈ Lpo.next α (s ∩ α.nodes_finset))
    (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv)
    (hind : ∀ t ⊂ s,
      ∀ (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
      (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv),
      is_indep hr₁ hr₂ hu hv hdn A B t σ₁ σ₂ hτ hτ₁ hτ₂) :
    minProb (Lpo.lin_node (par_comp α β hdn hu hr₁ hr₂) s x sorry (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) =
    minProb (Lpo.lin_node α (s ∩ α.nodes_finset) x hx.1 (σ₁.union τ₁ (dsj₁ hv))) (Mem.sep A ↑inv (dsj₁ hv)) *
      minProb (Lpo.lin_rec β (s ∩ β.nodes_finset) (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv)) := by
  unfold Lpo.lin_node
  have hu' := hu.trans (Finset.union_comm _ _)
  have hv' := hv.trans (Finset.inter_comm _ _)
  have hlab : (par_comp α β hdn hu hr₁ hr₂).lab x = upcast_lab (α.lab x) sorry := sorry -- LEMMA
  rw [hlab]; cases α.lab x with
  -- Case : β.lab y = ⊥
  | lab_bot => simp only [upcast_lab, minProb_bot, zero_mul]
  -- Case : β.lab y = Fork
  | lab_fork =>
    simp only [upcast_lab]
    have h₁ : (s ∩ α.nodes_finset).erase x = s.erase x ∩ α.nodes_finset := sorry
    have h₂ : s ∩ β.nodes_finset = s.erase x ∩ β.nodes_finset := sorry
    rw [h₁, h₂]
    refine hind (s.erase x) ?_ _ _ hτ hτ₁ hτ₂
    exact Finset.erase_ssubset (Finset.mem_of_mem_inter_left hx.1)
  -- Case : β.lab y = act
  | lab_act a =>
    rw [upcast_lab, minProb_bind, minProb_bind]
    rw [iInf_subtype', iInf_subtype']
    refine Eq.trans ?_ (@ENNReal.iInf_mul _ _ _ sorry sorry).symm
    refine (equiv_sem_upcast hu hv (act := act)).iInf_congr ?_
    intro ⟨μ, hμ⟩
--    simp only [id_eq, eq_mpr_eq_cast, Set.coe_setOf, Set.mem_setOf_eq]
    rw [← ENNReal.tsum_mul_right]
    refine tsum_congr' ?_ ?_
    · refine ⟨?_, ?_, ?_, ?_⟩
      · intro ⟨σ, hσ⟩
        refine ⟨σ₂.union σ (dsj₂₁ hu hv), ?_⟩
        sorry
      · sorry
      · sorry
      · sorry
    · intro ⟨σ, hσ⟩
      rw [mul_assoc]; refine congrArg₂ _ ?_ ?_
      · sorry
      · have h₂ : s ∩ β.nodes_finset = s.erase x ∩ β.nodes_finset := sorry
        obtain ⟨σ', τ, heq, hinv⟩ : ∃ σ' : Mem (u₁ \ v), ∃ τ : Mem v, σ = σ'.union τ (dsj₁ hv) ∧ τ ∈ inv := sorry
        rw [← Finset.erase_inter, h₂]
        simp only [heq, Set.mem_setOf_eq, id_eq, eq_mpr_eq_cast, Set.coe_setOf,
          Equiv.coe_fn_mk]
        rw [union_comm_assoc hu' hv']
        refine (hind (s.erase x) ?_ _ _ hinv hinv hτ₂).symm
        exact Finset.erase_ssubset (Finset.mem_of_mem_inter_left hx.1)
  | lab_test t => sorry

lemma par_comp_inductive_step'
    {s : Finset Node} {x : Node} (hx : x ∈ Lpo.next β (s ∩ β.nodes_finset))
    (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv)
    (hind : ∀ t ⊂ s,
      ∀ (σ₁ : Mem (u₁ \ v)) (σ₂ : Mem (u₂ \ v)) {τ τ₁ τ₂ : Mem v}
         (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv),
      is_indep hr₁ hr₂ hu hv hdn A B t σ₁ σ₂ hτ hτ₁ hτ₂) :
    minProb (Lpo.lin_node (par_comp α β hdn hu hr₁ hr₂) s x sorry (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) =
    minProb (Lpo.lin_rec α (s ∩ α.nodes_finset) (σ₁.union τ₁ (dsj₁ hv))) (Mem.sep A ↑inv (dsj₁ hv)) *
      minProb (Lpo.lin_node β (s ∩ β.nodes_finset) x hx.1 (σ₂.union τ₂ (dsj₂ hv))) (Mem.sep B ↑inv (dsj₂ hv)) := by
  rw [mul_comm, union_comm_assoc hu hv, sep_comm_assoc hu hv, par_comp_comm hu]
  have hu' := hu.trans (Finset.union_comm _ _)
  have hv' := hv.trans (Finset.inter_comm _ _)
  exact
    par_comp_inductive_step hr₂ hr₁ hu' hv' hdn.symm B A hx σ₂ σ₁ hτ hτ₂ hτ₁
      (flip_hind hr₁ hr₂ hu hv hdn A B hind)

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
    (hτ : τ ∈ inv) (hτ₁ : τ₁ ∈ inv) (hτ₂ : τ₂ ∈ inv) :
    minProb
      (Lpo.lin
        (par_comp α β hdn hu hr₁ hr₂)
        (σ₁.union (σ₂.union τ (dsj₂ hv)) (dsj₁₂ hu hv)))
      (Mem.sep A (Mem.sep B ↑inv (dsj₂ hv)) (dsj₁₂ hu hv)) =
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
          and_true, and_false, ↓reduceIte, and_self, mul_zero, mul_one]
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
        refine
          (iInf_congr fun i ↦
            (iInf_congr_Prop (Set.mem_union i _ _) fun _ ↦ rfl).trans
            iInf_or
            ).trans ?_
        rw [iInf_inf_eq, iInf_subtype', iInf_subtype']
        refine Eq.trans (congrArg₂ _ ?_ ?_) (inf_idem _)
        · nth_rw 1 [Lpo.lin_rec]; simp only [hne, ↓reduceIte]
          rw [minProb_nondet]
          refine Eq.trans ?_ (iInf_next_mul hne).symm
          refine iInf_congr fun ⟨y, hy⟩ ↦ ?_
          exact
            par_comp_inductive_step hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hind
        · nth_rw 2 [Lpo.lin_rec]
          simp only [↓reduceIte, hne']
          rw [minProb_nondet]
          refine Eq.trans ?_ (mul_iInf_next hne').symm
          refine iInf_congr fun ⟨y, hy⟩ ↦ ?_
          exact
            par_comp_inductive_step' hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hind
      -- Case 3: Next comes from α (β is empty)
      · nth_rw 1 [Lpo.lin_rec]; simp only [↓reduceIte, hne]
        rw [minProb_nondet, minProb_nondet]
        refine Eq.trans ?_ (iInf_next_mul hne).symm
        refine iInf_congr fun ⟨y, hy⟩ ↦ ?_
        exact
          par_comp_inductive_step hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hind
      -- Case 4: Next comes from β (α is empty)
      · nth_rw 2 [Lpo.lin_rec]; simp only [hne, ↓reduceIte]
        rw [minProb_nondet, minProb_nondet]
        refine Eq.trans ?_ (mul_iInf_next hne).symm
        refine iInf_congr fun ⟨y, hy⟩ ↦ ?_
        exact
          par_comp_inductive_step' hr₁ hr₂ hu hv hdn A B hy σ₁ σ₂ hτ hτ₁ hτ₂ hind
