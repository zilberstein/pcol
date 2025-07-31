import Mathlib

inductive Cmd (t : Type) (a : Type) where
  | skip : Cmd t a
  | seq : Cmd t a → Cmd t a → Cmd t a
  | par : Cmd t a → Cmd t a → Cmd t a
  | ifstmt : t → Cmd t a → Cmd t a → Cmd t a
  | while  : t → Cmd t a → Cmd t a
  | act : a → Cmd t a

def Node := ℕ
def Form := Set Node → Prop

def succ {a : Type} (x : a) (ord : Rel a a) : Set a :=
  fun y => ord x y ∧ ∀ z, ¬(ord x z ∧ ord z y)

def lev {a : Type} (x : a) (ord : Rel a a) : ℕ :=
  0
def lev_inv {a : Type} (n : ℕ) (ord : Rel a a) : Set a := { x : a | lev x ord = n }

def roots {a : Type} (ord : Rel a a) : Set a := { x ∈ ord.dom | ∀ y, ¬(ord y x) }

def CausalityRel (a : Type) :=
  { ord : Rel a a //
    -- ord is a strict partial order
    Transitive ord ∧ AntiSymmetric ord ∧ Irreflexive ord ∧
    -- ord is finitely preceeded
    (∀ x, Finite (ord.preimage {x})) ∧
    -- each level is finite
    (∀ n : ℕ, Finite (lev_inv n ord)) ∧
    -- ord is single-rooted
    (∃ x, roots ord = {x}) }

def Lpo_base (l : Type) [Bot l] :=
  (N : Set Node) × CausalityRel ↑N × (↑N → l) × (↑N → Form)

def is_valid_lpo {l : Type} [Bot l] : Lpo_base l → Prop
  | ⟨N, ord, lab, φ⟩ =>
      -- Bot nodes have no successors
      (∀ x : ↑N, lab x = ⊥ → succ x ord.val = ∅)
      -- Formulae todo

def Lpo (l : Type) [Bot l] :=
  { α : Lpo_base l // is_valid_lpo α }

def cast_rel {a : Type} (N : Set a) (r : Rel ↑N ↑N) : Rel a a :=
  fun x y =>
    if x ∈ N /\ y ∈ N then
      r x y
    else
      False

def DownCl {a : Type} (N M : Set a) (ord : Rel ↑M ↑M) : Prop :=
  N ⊆ M ∧ ∀ x ∈ N, ∀ y ∈ M, ord

  ↑(ord.preimage {Subtype.map id h x}) ⊆ N

def DownClSubs {a : Type} (N M : Set a) (ord : Rel ↑M ↑M) : Prop :=
  let p := N ⊆ M
  let q := DownCl N M ord p

instance {l : Type} [Bot l] : LE (Lpo l) := by {
  constructor; intros α β
  rcases α with ⟨ ⟨N, ord, lab, φ⟩, h⟩
  rcases β with ⟨ ⟨N', ord', lab', φ'⟩, h'⟩
  let p := N ⊆ N'
}

instance {l : Type} [Bot l] : LE (Lpo l) := by {
  constructor; intros α β
  rcases α with ⟨ ⟨N, ord, lab, φ⟩, h⟩
  rcases β with ⟨ ⟨N', ord', lab', φ'⟩, h'⟩
  exact (N ⊆ N' ∧ N ≠ N')
}

-- lemma strict_subs {a : Type} (X Y : Set a) :
--   X ⊆ Y →
--   X ≠ Y →
--   ∃ x ∈ Y, x ∉ X := by {
--     intro hsub hneq
--     obtain ⟨x, h⟩  := by exact (Function.ne_iff.1 hneq)


--     }

--     exact (Function.ne_iff X Y)
--   }

instance {l : Type} [Bot l] [Preorder l] : Preorder (Lpo l) where
  le_refl := by {
    intro α
    constructor
    exact subset_rfl
  }
  le_trans := by {
    intro α β γ ⟨hs1, hn1⟩ ⟨hs2, hn2⟩
    constructor
    · exact subset_trans hs1 hs2
    · intro hc
      apply hn2

      have h : ∃ x ∈ α.1.fst, x ∉ γ.1.fst := by {

      }
  }


--def singleton {l : Type} (n : Node) (v : l) := ({n}, )

noncomputable def sem {t a st : Type} (semt : t → st → Bool) (sema : a → st → PMF st)
  (c : Cmd t a) (s : st) : PMF st :=
  match c with
  | Cmd.skip => PMF.pure s
  | Cmd.seq c1 c2 => PMF.bind (sem semt sema c1 s) (sem semt sema c2)
  | Cmd.par _ _ => PMF.pure s
  | Cmd.ifstmt b c1 c2 =>
      if semt b s then sem semt sema c1 s else sem semt sema c2 s
  | Cmd.while _ _ => PMF.pure s
  | Cmd.act a => sema a s
