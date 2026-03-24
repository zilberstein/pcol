import Mathlib
import Pcol.Semantics.Pom.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Isomorphism

def Pomfin (l : Type) [Bot l] : Type := Quotient (@Lpofin.instSetoid l _)

instance {l : Type} [Bot l] : Coe (Pomfin l) (Pom l) where
  coe p := p.lift
    (fun a => Quotient.mk' a.val)
    (fun _ _ heq => Quotient.sound heq)

namespace Pom

noncomputable def trunc {l : Type} [Bot l] (p : Pom l) (n : ℕ) : Pomfin l :=
  p.lift
    (fun (a : Lpo l) ↦ Quotient.mk (@Lpofin.instSetoid l _) (a.trunc n))
    (fun _ _ h ↦ Quotient.eq_iff_equiv.2 (Lpo.trunc_equiv h))

end Pom

def lift_finset_equiv {S T : Finset Node} (e : Equiv S T) : Equiv S.toSet T.toSet := e

def perm_equivs {l : Type} [Bot l] (n : ℕ) (p : Node → Node) (a : Lpo l) : Set (Node ≃ Node) :=
  { e : Node ≃ Node | ∀ x ∈ (a.trunc n).val.nodes, p x = e x }

private structure TreeNode {l : Type} [Bot l] [LE l] (a b : Lpo l) : Type where
  n : ℕ
  -- Perm is a permutation
  perm : Node → Node
  -- The domain of perm must effectively be only the nodes of a.trunc n, otherwise
  -- there are infinitely many perm functions that have the same effect. This makes
  -- TreeNode effectively an equivalence class
  hdom : ∀ x ∉ (a.trunc n).val.nodes, perm x = default
  -- This guarantees that perm is a bijection on it's restricted domain and codomain
  heq : (perm_equivs n perm a).Nonempty
  le_b : ∀ e ∈ perm_equivs n perm a, (a.trunc n).val.permute e ≤ b

attribute [ext] TreeNode

namespace TreeNode

def dom {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  (a.trunc t.n).val.nodes

def range {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  t.perm '' (a.trunc t.n).val.nodes

lemma root_nodes {l : Type} [Bot l] (a : Lpo l) :
  (a.trunc 0).val.nodes = {Classical.choose a.property.rel.single_rooted} := by sorry

noncomputable def root {l : Type} [Bot l] [LE l] (a b : Lpo l) : TreeNode a b :=
  let x := Classical.choose a.property.rel.single_rooted
  let y := Classical.choose b.property.rel.single_rooted
  let b₀ := Lpo.singleton y (b.lab y)
  {
    n := 0
    perm z := if z = x then y else default
    hdom := by
      intro z hz; simp; intro h; subst h
      simp [Lpo.trunc, Lpo.nodes] at hz
      sorry
--      have h := Classical.choose_spec a.property.rel.single_rooted
    heq := by
      let f z := if z = x then y else if z = y then x else z
      let e : Node ≃ Node := {
        toFun := f
        invFun := f
        left_inv := by intro z; by_cases hx : z = x <;> by_cases hy : z = y <;> simp [hx, hy, f]
        right_inv := by intro z; by_cases hx : z = x <;> by_cases hy : z = y <;> simp [hx, hy, f]
      }
      refine ⟨e, ?_⟩; intro z hz; rw [root_nodes] at hz; simp at *
      subst hz; unfold x; simp [e, f, x]
    le_b := by
      intro e he; sorry
  }


lemma trunc_nodes_mono {l : Type} [Bot l] {a : Lpo l} {n m : ℕ}
  (hle : n ≤ m) : (a.trunc n).val.nodes ⊆ (a.trunc m).val.nodes := by {
  simp [Lpo.trunc, Lpofin.nodes, Lpo.nodes]
  intro x hx hlev; exact ⟨hx, le_trans hlev hle⟩
}

instance {l : Type} [Bot l] [LE l] {a b : Lpo l} : LE (TreeNode a b) where
  le t u := t.n ≤ u.n ∧ ∀ x ∈ TreeNode.dom t, t.perm x = u.perm x

instance {l : Type} [Bot l] [Preorder l] {a b: Lpo l} : Preorder (TreeNode a b) where
  le_refl t := by refine ⟨le_refl _, fun x => ?_⟩; simp
  le_trans t u v := by {
    intro ⟨hn₁, heq₁⟩ ⟨hn₂, heq₂⟩
    refine ⟨le_trans hn₁ hn₂, ?_⟩
    intro x hx; exact Eq.trans (heq₁ x hx) (heq₂ x (trunc_nodes_mono hn₁ hx))
  }

instance {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} : PartialOrder (TreeNode a b) where
  le_antisymm t u := by {
    intro ⟨hn₁, heq₁⟩ ⟨hn₂, heq₂⟩
    have hn := le_antisymm hn₁ hn₂
    ext x
    · exact hn
    · by_cases hx : x ∈ (a.trunc t.n).val.nodes
      · exact heq₁ x hx
      · rw [t.hdom _ hx]; rw [hn] at hx; rw [u.hdom _ hx]
  }

-- lemma perm_nodes {l : Type} [Bot l] [Preorder l] {a b : Lpo l} {t : TreeNode a b} :
--     t.nodes = t.perm '' TreeNode.dom t := by
--   unfold dom; ext x; simp; constructor
--   · intro hx; rcases t.heq with ⟨e, heq⟩; use e.symm x
--     have hs : e.symm x ∈ (a.trunc t.n).val.nodes := by
--       simp [perm_equivs] at heq

--     refine ⟨hs, ?_⟩
--     rw [heq _ hs]; exact Equiv.apply_symm_apply _ _
--   · intro ⟨y, hy, hp⟩; rw [← hp]; exact t.hrange _ hy

lemma le_and_n_eq {l : Type} [Bot l] [Preorder l] {a b : Lpo l} {t u : TreeNode a b}
    (hle : t ≤ u) (hn : t.n = u.n) : t = u := by
  rcases hle with ⟨_, hp⟩;
  have hp : t.perm = u.perm := by
    ext x; by_cases hx : x ∈ TreeNode.dom t
    · exact hp _ hx
    · rw [t.hdom _ hx]; unfold TreeNode.dom at hx; rw [hn] at hx; rw [u.hdom _ hx]
  ext x <;> simp [hn, hp]

lemma lt_iff {l : Type} [Bot l] [Preorder l] {a b : Lpo l} {t u : TreeNode a b} :
  t < u ↔ t.n < u.n ∧ ∀ x ∈ TreeNode.dom t, t.perm x = u.perm x := by {
    constructor
    · intro ⟨⟨hn, hex⟩, hc⟩; refine ⟨?_, hex⟩
      · refine Nat.lt_iff_le_and_not_ge.2 ⟨hn, fun h => hc ?_⟩
        cases Nat.lt_or_eq_of_le hn with
        | inl hlt => apply Nat.not_lt_of_le at h; contradiction
        | inr heq => exact le_of_eq (Eq.symm (le_and_n_eq ⟨hn, hex⟩ heq))
    · intro ⟨hn, hex⟩; refine ⟨⟨Nat.le_of_lt hn, hex⟩, fun hc => ?_⟩
      have h := hc.1; linarith
}

lemma covBy_between {l : Type} [Bot l] [Preorder l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : ∃ v, t ⋖ v ∧ v ≤ u ∧ v.n = t.n + 1 := by
  rcases lt_iff.mp hlt with ⟨hn, hp⟩
  let nodes := u.perm '' (a.trunc (t.n + 1)).val.nodes
  have h : ∀ x, ∃ y, (x ∈ (a.trunc (t.n + 1)).val.nodes → y = u.perm x) ∧ (x ∉ (a.trunc (t.n + 1)).val.nodes → y = default) := by
    intro x; by_cases hx : x ∈ (a.trunc (t.n + 1)).val.nodes
    · use u.perm x; simp [hx]
    · use default; simp [hx]
  choose f hf using h
  use {
    n := t.n + 1
    perm := f
    hdom := fun x hx ↦ (hf x).2 hx
    heq := by
      obtain ⟨e, he⟩ := u.heq
      use e; intro x hx
      rw [(hf x).1 hx, he x (trunc_nodes_mono (by linarith) hx)]
    le_b := by
      intro e he; sorry -- Need some more lemmas for this
  }
  refine ⟨⟨lt_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_, rfl⟩
  · simp
  · intro x hx; refine Eq.trans (hp _ hx) ?_
    exact Eq.symm ((hf x).1 (trunc_nodes_mono (Nat.le_succ _) hx))
  · intro v hlt hc
    rcases lt_iff.mp hlt with ⟨hlt, _⟩
    rcases lt_iff.mp hc with ⟨hlt', _⟩; simp at hlt'; linarith
  · exact ⟨by linarith, fun y hy ↦ (hf y).1 hy⟩

instance {l : Type} [Bot l] [Preorder l] {a b : Lpo l} : IsStronglyAtomic (TreeNode a b) where
  exists_covBy_le_of_lt := fun _ _ hlt ↦ match covBy_between hlt with | ⟨v, h₁, h₂, _⟩ => ⟨v, h₁, h₂⟩

lemma cov_by_iff {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} {t u : TreeNode a b} :
  t ⋖ u ↔ t.n + 1 = u.n ∧ ∀ x ∈ TreeNode.dom t, t.perm x = u.perm x := by {
  constructor
  · intro ⟨hlt, hnlt⟩; constructor
    · have hn := Nat.succ_le_of_lt (lt_iff.1 hlt).1
      cases Nat.lt_or_eq_of_le hn with
      | inr heq => exact heq
      | inl hc =>
        obtain ⟨v, ⟨⟨hlt', _⟩, hvu, hnn⟩⟩ := covBy_between hlt
        have hhh := hnlt hlt'
        have h := eq_iff_le_not_lt.mpr ⟨hvu, hhh⟩; subst h; exact Eq.symm hnn
    · rcases hlt with ⟨⟨_, hf⟩, _⟩; exact hf
  · intro ⟨hn, hp⟩; refine ⟨lt_iff.mpr ⟨by linarith, hp⟩, ?_⟩
    · intro v hv hu
      have hn₁ := (lt_iff.mp hv).1
      have hn₂ := (lt_iff.mp hu).1
      linarith
}

def covBy_injection {l : Type} [Bot l] [Preorder l] {a b : Lpo l} (t : TreeNode a b)
    (u : {u // t ⋖ u}) (x : ↑(a.rel.lev ⁻¹' {t.n + 1})) : ↑(b.rel.lev ⁻¹' {t.n + 1}) :=
  Subtype.mk (u.val.perm x.val) (by {
    sorry
  })

lemma covBy_equiv {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} (t : TreeNode a b) :
    Function.Injective (covBy_injection t) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩ h; unfold covBy_injection at h; simp at h
  rcases cov_by_iff.mp hu with ⟨hun, hup⟩
  rcases cov_by_iff.mp hv with ⟨hvn, hvp⟩
  ext x
  · simp [← hun, ← hvn]
  · simp; by_cases hx : x ∈ dom t
    · rw [← hup _ hx, hvp _ hx]
    · by_cases hx' : x ∈ a.rel.lev ⁻¹' {t.n + 1}
      · have h := congrFun h ⟨x, hx'⟩; simp at h; exact h
      · have h : x ∉ dom u := by
          simp [dom, Lpo.trunc, Lpo.nodes] at *
          intro hx''; rw [← hun]
          exact (Nat.succ_le_of_lt (hx hx'')).lt_iff_ne.mpr (Ne.symm hx')
        rw [u.hdom _ h]; unfold dom at h; rw [← hun, hvn] at h
        rw [v.hdom _ h]

lemma finite_branching {l : Type} [Bot l] [PartialOrder l] (a b : Lpo l)
  (t : TreeNode a b) : { u | t ⋖ u }.Finite := by {
    refine @Finite.of_injective _ _ ?_ (covBy_injection t) (covBy_equiv _)
    exact @Pi.finite _ _ (a.property.rel.fin_lev _) (fun _ => b.property.rel.fin_lev _)
  }

lemma perm_equivs_permute {l : Type} [Bot l] {n : ℕ} {p : Node → Node} {a : Lpo l} :
    ∀ e ∈ perm_equivs n p a, ∀ e' ∈ perm_equivs n p a, (a.trunc n).val.permute e = (a.trunc n).val.permute e' := by
  intro e he e' he'
  have heq := fun x hx ↦ Eq.trans (Eq.symm (he x hx)) (he' x hx)
  unfold Lpo.permute; refine lpo_eq_iff.mpr ⟨?_, ?_, ?_, ?_⟩
  · exact Set.image_congr heq
  · ext x y; sorry
  · sorry
  · sorry

lemma has_infinite_path {l : Type} [Preorder l] [OrderBot l] {a b : Lpo l}
  (hle : ∀ n, ∃ e, (a.trunc n).val.permute e ≤ b) : (Set.Ici (root a b)).Infinite := by {
    have h : ∀ n, ∃ p : Node → Node, ∃ e : Node ≃ Node,
        (∀ x ∈ (a.trunc n).val.nodes, p x = e x) ∧
        (∀ x ∉ (a.trunc n).val.nodes, p x = default) ∧
        (a.trunc n).val.permute e ≤ b := by
      intro n; obtain ⟨e, he⟩ := hle n
      have h : ∀ x : Node, ∃ y, (x ∈ (a.trunc n).val.nodes → y = e x) ∧ (x ∉ (a.trunc n).val.nodes → y = default) := by
        intro x; by_cases hx : x ∈ (a.trunc n).val.nodes
        · use e x; simp [hx]
        · use default; simp [hx]
      choose p hp using h
      refine ⟨p, e, fun x hx ↦ (hp x).1 hx, fun x hx ↦ (hp x).2 hx, he⟩
    choose g hg using h
    let f (i : ℕ) : TreeNode a b := {
      n := i
      perm := g i
      hdom := by intro x hx; have ⟨_, _, h, _⟩ := hg i; exact h x hx
      heq := by obtain ⟨e, ⟨he, _⟩⟩ := hg i; exact ⟨e, fun x hx ↦ he x hx⟩
      le_b := by
        obtain ⟨e, he, _, hle⟩ := hg i; intro e' he'
        rw [perm_equivs_permute e' he' e he]; exact hle
    }
    have hsub : f '' Set.univ ⊆ Set.Ici (root a b) := by {
      simp [Set.Ici, f, Set.range]; intro i; refine ⟨bot_le, ?_⟩
      intro x hx; simp; sorry
    }
    refine Set.Infinite.mono hsub ?_
    refine Set.Infinite.image ?_ Set.infinite_univ
    simp [f]; intro i _ j _; simp; exact fun hij _ ↦ hij
  }

end TreeNode

theorem pom_ge_iff_ge_fin {l : Type}
  [CompletePartialOrder l] [OrderBot l] {p q : Pom l}
  (hle : ∀ n, p.trunc n ≤ q) : p ≤ q := by {
  have ⟨a, ha⟩ := Quotient.exists_rep p
  have ⟨b, hb⟩ := Quotient.exists_rep q
  subst ha; subst hb
  unfold Pom.trunc at hle; simp at hle
  have hle' : ∀ n, ∃ e, (a.trunc n).val.permute e ≤ b := by
    intro n; have ⟨a', ha', hlea⟩ := Pom.le_iff_2.mp (hle n) b rfl
    have ⟨e, he⟩ := Quotient.exact ha'
    refine ⟨e, ?_⟩; rw [he]; exact hlea
  rcases exists_seq_covby_of_forall_covby_finite
          (TreeNode.finite_branching a b)
          (TreeNode.has_infinite_path hle') with ⟨f, h₀, hsucc⟩
  let p z := (f (a.rel.lev z)).perm z

  obtain ⟨e, he⟩ := permute_chain

  have e : a ≈ a' := by sorry -- Need a lemma for this
  refine ⟨a', b, ?_, Quotient.sound heq, rfl⟩
  unfold a'; refine (isLUB_le_iff (lpo_sup_is_lub ?_ ?_)).2 ?_
  · simp [DirectedOn]; intro i j; use (max i j)
    have hle : ∀ k l, k ≤ l
    constructor
    · sorry
    · sorry
  · use TreeNode.getLpo (f 0); simp
  · unfold upperBounds; simp; intro i
    rcases hi : f i with ⟨j, c, hc⟩; simp [TreeNode.getLpo]
    exact hc.2
}
