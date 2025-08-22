import Mathlib

inductive Cmd (t : Type) (a : Type) where
  | skip : Cmd t a
  | seq : Cmd t a → Cmd t a → Cmd t a
  | par : Cmd t a → Cmd t a → Cmd t a
  | ifstmt : t → Cmd t a → Cmd t a → Cmd t a
  | while  : t → Cmd t a → Cmd t a
  | act : a → Cmd t a

def Node := ℕ
instance : Inhabited Node where
  default := (0 : ℕ)

def Form (α : Type) := Set α → Prop

@[ext]
lemma form_ext {α : Type} {φ ψ : Form α} (h : ∀ x, φ x = ψ x) : φ = ψ := by sorry

def form_true {α : Type} : Form α := fun _ => True
def form_false {α : Type} : Form α := fun _ => False
def and {α : Type} (p : Form α) (q : Form α) : Form α := fun v => p v ∧ q v
def literal {α : Type} (x : α) : Form α := fun v => x ∈ v

def sat {α : Type} (p : Form α) : Prop := ∃ v, p v

def vars {α : Type} (p : Form α) : Set α := ∅
--  { x : Node | ∀ v, p v → p (fun y => if x = y then ¬(v y) else v y) }

def succ {a : Type} (x : a) (ord : Rel a a) : Set a :=
  fun y => ord x y ∧ ∀ z, ¬(ord x z ∧ ord z y)

def lev_inv {a : Type} (n : ℕ) (ord : Rel a a) : Set a := ∅

def roots {a : Type} (ord : Rel a a) : Set a := { x : a | ∀ y, ¬(ord y x) }

def is_succ_chain {α : Type} (ord : Rel α α) (l : List α) : Prop :=
  match l with
  | [] => False
  | List.cons x xs =>
    (xs.foldr (fun (x : α) (acc : α × Prop) => (x, acc.2 ∧ x ∈ succ acc.1 ord)) (x, True)).2

noncomputable def lev {a : Type} (x : a) (ord : Rel a a) : ℕ :=
  sInf { n : ℕ | ∃ l : List a, n = l.length - 1 ∧ is_succ_chain ord l ∧ l.getLast? = Option.some x }

structure is_causality_rel {α : Type} (ord : Rel α α) : Prop where
  -- ord is a strict partial order
  trans : Transitive ord
  antisymm : AntiSymmetric ord
  irrefl : Irreflexive ord
  -- ord is finitely preceeded
  wf : WellFounded ord
  -- each level is finite
  fin_lev: ∀ n : ℕ, (lev_inv n ord).Finite
  -- ord is single-rooted
  single_rooted : ∃ x, roots ord = {x}

structure Lpo_base (l : Type) [Bot l] where
  nodes : Set Node
  rel : Rel ↑nodes ↑nodes
  lab : ↑nodes → l
  form : ↑nodes → Form ↑nodes

structure is_valid_lpo {l : Type} [Bot l] (a : Lpo_base l) : Prop where
  -- The order is valid
  rel : is_causality_rel a.rel
  -- Bot nodes have no successors
  bot : ∀ x : ↑a.nodes, a.lab x = ⊥ → succ x a.rel = ∅
  -- Formulae
  form : ∀ x : ↑a.nodes, sat (a.form x) ∧ (∀ y ∈ vars (a.form x), a.rel y x) ∧
          ∀ z, a.rel x z → ∀ v, a.form z v → a.form x v


def Lpo (l : Type) [Bot l] := { α : Lpo_base l // is_valid_lpo α }

namespace Lpo

def nodes {l : Type} [Bot l] (a : Lpo l) : Set Node := a.val.nodes
def rel {l : Type} [Bot l] (a : Lpo l) : Rel ↑a.nodes ↑a.nodes := a.val.rel
def lab {l : Type} [Bot l] (a : Lpo l) : ↑a.nodes → l := a.val.lab
def form {l : Type} [Bot l] (a : Lpo l) : ↑a.nodes → Form ↑a.nodes := a.val.form

def bots {l : Type} [Bot l] (a : Lpo l) : Set ↑a.nodes := { x | a.lab x = ⊥}

end Lpo

def castNode {N M : Set Node} (x : ↑N) (h : N ⊆ M) : ↑M := ⟨x.val, h x.property⟩

def castRel {N M : Set Node} (r : Rel ↑N ↑N) (h : M ⊆ N) : Rel ↑M ↑M :=
  fun x y => r (castNode x h) (castNode y h)

lemma castRel_iff {N M : Set Node} {r : Rel ↑N ↑N} {h : M ⊆ N} {x y : ↑M} :
  r (castNode x h) (castNode y h) ↔ (castRel r h) x y := by {
    simp [castNode, castRel]
  }

def castForm {N M : Set Node} (p : Form ↑N) (h : M ⊆ N) : Form ↑M :=
  fun (v : Set ↑M) => p ((castNode · h) '' v)

def is_down_closed {N : Set Node} (ord : Rel ↑N ↑N) (X : Set Node) (h : X ⊆ N) : Prop :=
  ∀ x (hx : x ∈ X), ∀ y : ↑N, ord y ⟨x, h hx⟩ → y.val ∈ X

def up_closure {N M : Set Node} (ord : Rel ↑N ↑N) (X : Set ↑M) (h : M ⊆ N) : Set ↑N :=
  { x : ↑N | ∃ y ∈ X, ord (castNode y h) x }

structure LE_Lpo {l : Type} [LE l] [Bot l] (a b : Lpo l) (hsub : a.nodes ⊆ b.nodes): Prop where
  downcl : is_down_closed b.rel a.nodes hsub
  rel : a.rel = castRel b.rel hsub
  lab : ∀ x : ↑a.nodes, a.lab x ≤ b.lab (castNode x hsub)
  form : ∀ x : ↑a.nodes, a.form x = castForm (b.form (castNode x hsub)) hsub
  succ : ∀ x : ↑a.nodes, Subtype.val '' succ x a.rel =
    succ (castNode x hsub) b.rel \ up_closure b.rel a.bots hsub

instance {l : Type} [LE l] [Bot l] : LE (Lpo l) where
  le a b := ∃ h : a.nodes ⊆ b.nodes, LE_Lpo a b h

lemma castNode_idem {N : Set Node} {x : ↑N} {h : N ⊆ N} : castNode x h = x := by unfold castNode; simp
lemma castRel_idem {N : Set Node} {r : Rel ↑N ↑N} {h : N ⊆ N} : castRel r h = r := by
  unfold castRel; ext x y; rw [castNode_idem,castNode_idem]
lemma castForm_idem {N : Set Node} {p : Form ↑N} {h : N ⊆ N} : castForm p h = p := by
  unfold castForm
  have h : (fun x ↦ castNode x h) = id := by ext x; rw [castNode]; simp
  rw [h]; simp

lemma up_closure_same_empty {l : Type} [Bot l] {a : Lpo l} {h : a.nodes ⊆ a.nodes} :
  up_closure a.rel a.bots h = ∅ := by {
    match a with
    | ⟨a', ⟨_, hbot, _⟩⟩ =>
      unfold up_closure; ext x; constructor
      · rintro ⟨y, hybot, hrel⟩
        have h := hbot y hybot
        rw [castNode_idem] at hrel
        sorry
        --This proof sets a bit tricky, and I think it depends on Well-foundedness of rel
      · intro hc; contradiction
}

lemma castNode_trans {X Y Z : Set Node} {h₁ : X ⊆ Y} {h₂ : Y ⊆ Z} {h₃ : X ⊆ Z} {x : ↑X} :
  castNode x h₃ = castNode (castNode x h₁) h₂ := by unfold castNode; simp

instance {l : Type} [Preorder l] [Bot l] : Preorder (Lpo l) where
  le_refl a := by {
    use (subset_refl a.nodes); constructor
    · intro x hx y hy; simp
    · rw [castRel_idem]
    · intro x; rw [castNode_idem]
    · intro x; rw [castForm_idem, castNode_idem]
    · intro x; rw [castNode, up_closure_same_empty]; simp
  }
  le_trans a b c := by {
    rintro ⟨hs1, hab⟩ ⟨hs2, hbc⟩
    use (subset_trans hs1 hs2); constructor
    · intro x hx y hyx
      have h := hbc.1 x (hs1 hx) y hyx
      exact hab.1 x hx ⟨y.val, h⟩ (by sorry)
    · rw [hab.rel, hbc.rel]; ext x y
      unfold castRel
      rw [← castNode_trans (h₃ := subset_trans hs1 hs2)]
      rw [← castNode_trans (h₃ := subset_trans hs1 hs2)]
    · intro x; refine le_trans (hab.lab _) ?_
      rw [castNode_trans (h₃ := subset_trans hs1 hs2)]; exact hbc.lab _
    · intro x; refine Eq.trans (hab.form _) ?_
      sorry -- Easy, but I don't feel like doing it right now
    · intro x; refine Eq.trans (hab.succ _) ?_
      sorry -- Need some lemmas about succ
  }

lemma lpo_eq_iff {l : Type} [Bot l] {a b : Lpo l} :
  a = b ↔
  ∃ h : a.nodes = b.nodes,
    a.rel = castRel b.rel (Eq.subset h) ∧
    a.lab = b.lab ∘ (castNode · (Eq.subset h)) ∧
    a.form = (castForm · (Eq.subset h)) ∘ b.form ∘ (castNode · (Eq.subset h)) := by {
  constructor
  · intro heq; rw [heq]; use rfl; simp [castRel_idem, castNode_idem, castForm_idem]
    refine ⟨?_, ?_⟩
    · ext X; simp
    · ext X x; simp
  · rintro ⟨heq, hrel, hlab, hform⟩
    apply Subtype.ext; cases ↑a; sorry
}

instance {l : Type} [PartialOrder l] [Bot l] : PartialOrder (Lpo l) where
  le_antisymm a b := by {
    rintro ⟨h1, hab⟩; rintro ⟨h2, hba⟩
    have heq := le_antisymm h1 h2
    refine lpo_eq_iff.2 ?_
    refine ⟨heq, hab.rel, ?_, ?_⟩
    · ext x; simp; refine le_antisymm (hab.lab _) ?_
      sorry -- need to show that castNode does nothing when a.nodes = b.nodes
    · ext1 x; exact hab.form x
  }

def lpo_base_sup {l : Type} [SupSet l] [Bot l] (s : Set (Lpo l)) : Lpo_base l := {
  nodes := ⋃ a ∈ s, a.nodes
  rel x y := ∃ a ∈ s, ∃ hx : x.val ∈ a.nodes, ∃ hy : y.val ∈ a.nodes, a.rel ⟨x, hx⟩ ⟨y, hy⟩
  lab x := sSup { l | ∃ a ∈ s, ∃ h : x.val ∈ a.nodes, l = a.lab ⟨x.val, h⟩ }
  form x := sorry
}

instance {l : Type} [Bot l] : Inhabited (Lpo l) where
  default := ⟨{
    nodes := {default}
    rel _ _ := False
    lab _ := ⊥
    form _ := form_true
  },
  by {
    constructor
    · simp; constructor
      · intro _ _ _ hc; contradiction
      · intro _ _ hc; contradiction
      · intro _ hc; contradiction
      · sorry
      · sorry
      · use default; unfold roots; ext x; simp
        rcases x with ⟨x, h⟩; simp at h; simp [h]
    · simp; intro x hx; unfold succ; ext X; simp; intro hc; contradiction
    · simp; unfold form_true
      refine ⟨⟨default, ?_⟩, ?_⟩
      · simp
      · intro x hx; sorry
  }⟩

noncomputable instance {l : Type} [SupSet l] [Bot l] : SupSet (Lpo l) where
  sSup s : Lpo l := by {
    by_cases h : is_valid_lpo (lpo_base_sup s)
    · exact ⟨lpo_base_sup s, h⟩
    · exact default
  }

theorem lpo_sup_of_directed {l : Type} [SupSet l] [LE l] [Bot l] {d : Set (Lpo l)}
  {h : DirectedOn (· ≤ ·)  d} :
  ∃ hv, sSup d = ⟨lpo_base_sup d, hv⟩ := by {
  have hv : is_valid_lpo (lpo_base_sup d) := by {
    unfold lpo_base_sup; constructor
    · simp; constructor
      · rintro x y z ⟨a, ha, hxa, hya, harel⟩ ⟨b, hb, hyb, hzb, hbrel⟩
        rcases h a ha b hb with ⟨c, hc, hac, hbc⟩
        refine ⟨c, hc, hac.1 hxa, hbc.1 hzb, ?_⟩
        refine c.property.rel.trans ?_ ?_ (y := castNode y ?_)
        · sorry
        · rw [hac.2.rel] at harel; sorry
        · sorry
      · sorry
      · sorry
      · sorry
      · sorry
      · sorry
    · simp; rintro x a ⟨had, hxa⟩ hsup
      sorry
    · simp; intro x a; sorry
  }
  use hv; simp [sSup]
  rw [dite_cond_eq_true]; refine propext ⟨fun _ => trivial, fun _ => hv⟩
}
