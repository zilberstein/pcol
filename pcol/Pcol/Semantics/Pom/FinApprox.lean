import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice
import Mathlib.Order.Atoms
import Mathlib.Order.KonigLemma

import Pcol.Semantics.Pom.Basic
import Pcol.Semantics.Lpo.FinApprox

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

private structure TreeNode {l : Type} [Bot l] [LE l] (a b : Lpo l) : Type where
  n : ℕ
  X : Set Node
  -- Perm is a permutation
  perm : (a.trunc n).nodes ≃ X
  -- The domain of perm must effectively be only the nodes of a.trunc n, otherwise
  -- there are infinitely many perm functions that have the same effect. This makes
  -- TreeNode effectively an equivalence class
--  hdom : ∀ x ∉ (a.trunc n).val.nodes, perm x = default
  -- This guarantees that perm is a bijection on it's restricted domain and codomain
--  heq : (perm_equivs n perm a).Nonempty
  le_b : (a.trunc n).val.permute perm ≤ b

attribute [ext] TreeNode

namespace TreeNode

def dom {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  (a.trunc t.n).val.nodes

def range {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  t.X
--  t.perm '' (a.trunc t.n).val.nodes

lemma root_nodes {l : Type} [Bot l] (a : Lpo l) :
  (a.trunc 0).val.nodes = {Classical.choose a.property.rel.single_rooted} := by sorry

noncomputable def root {l : Type} [Bot l] [LE l] (a b : Lpo l) : TreeNode a b :=
  let x := Classical.choose a.property.rel.single_rooted
  let y := Classical.choose b.property.rel.single_rooted
  let b₀ := Lpo.singleton y (b.lab y)
  {
    n := 0
    X := {y}
    perm := {
      toFun _ := ⟨y, Set.mem_singleton _⟩
      invFun _ := ⟨x, by sorry⟩
      left_inv := by sorry
      right_inv := sorry
    }
    le_b := by
      sorry
  }


lemma trunc_nodes_mono {l : Type} [Bot l] {a : Lpo l} {n m : ℕ}
  (hle : n ≤ m) : (a.trunc n).val.nodes ⊆ (a.trunc m).val.nodes := by {
  simp [Lpo.trunc, Lpofin.nodes, Lpo.nodes]
  sorry -- intro x hx hlev; exact ⟨hx, le_trans hlev hle⟩
}

instance {l : Type} [Bot l] [LE l] {a b : Lpo l} : LE (TreeNode a b) where
  le t u :=
    t.n ≤ u.n ∧
    Lpo.PermExt t.perm u.perm

instance {l : Type} [Bot l] [Preorder l] {a b: Lpo l} : Preorder (TreeNode a b) where
  le_refl t := by sorry -- refine ⟨le_refl _, fun x => ?_⟩; simp
  le_trans t u v := by {
    intro ⟨hn₁, heq₁⟩ ⟨hn₂, heq₂⟩
    refine ⟨le_trans hn₁ hn₂, ?_⟩
    sorry --intro x; exact Eq.trans (heq₁ x) (heq₂ ⟨x.val, trunc_nodes_mono hn₁ x.property⟩)
  }

instance {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} : PartialOrder (TreeNode a b) where
  le_antisymm t u := by {
    intro ⟨hn₁, heq₁⟩ ⟨hn₂, heq₂⟩
    have hn := le_antisymm hn₁ hn₂
    ext x
    · exact hn
    · sorry
    · sorry

      -- by_cases hx : x ∈ (a.trunc t.n).val.nodes
      -- · exact heq₁ x hx
      -- · rw [t.hdom _ hx]; rw [hn] at hx; rw [u.hdom _ hx]
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
  rcases hle with ⟨_, hp⟩; sorry
  -- have hp : t.perm = u.perm := by
  --   ext x; by_cases hx : x ∈ TreeNode.dom t
  --   · exact hp _ hx
  --   · rw [t.hdom _ hx]; unfold TreeNode.dom at hx; rw [hn] at hx; rw [u.hdom _ hx]
  -- ext x <;> simp [hn, hp]

lemma lt_iff {l : Type} [Bot l] [Preorder l] {a b : Lpo l} {t u : TreeNode a b} :
  t < u ↔ t.n < u.n ∧ Lpo.PermExt t.perm u.perm := by {
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
    (hlt : t < u) : ∃ v, t ⋖ v ∧ v ≤ u ∧ v.n = t.n + 1 := by sorry
--   rcases lt_iff.mp hlt with ⟨hn, hp⟩
-- --  let nodes := u.perm '' (a.trunc (t.n + 1)).val.nodes
--   have h : ∀ x, ∃ y, (x : (a.trunc (t.n + 1)).val.nodes → y = u.perm x) ∧ (x ∉ (a.trunc (t.n + 1)).val.nodes → y = default) := by
--     intro x; by_cases hx : x ∈ (a.trunc (t.n + 1)).val.nodes
--     · use u.perm x; simp [hx]
--     · use default; simp [hx]
--   choose f hf using h
--   use {
--     n := t.n + 1
--     perm := f
--     hdom := fun x hx ↦ (hf x).2 hx
--     heq := by
--       obtain ⟨e, he⟩ := u.heq
--       use e; intro x hx
--       rw [(hf x).1 hx, he x (trunc_nodes_mono (by linarith) hx)]
--     le_b := by
--       intro e he; sorry -- Need some more lemmas for this
--   }
--   refine ⟨⟨lt_iff.mpr ⟨?_, ?_⟩, ?_⟩, ?_, rfl⟩
--   · simp
--   · intro x hx; refine Eq.trans (hp _ hx) ?_
--     exact Eq.symm ((hf x).1 (trunc_nodes_mono (Nat.le_succ _) hx))
--   · intro v hlt hc
--     rcases lt_iff.mp hlt with ⟨hlt, _⟩
--     rcases lt_iff.mp hc with ⟨hlt', _⟩; simp at hlt'; linarith
--   · exact ⟨by linarith, fun y hy ↦ (hf y).1 hy⟩

instance {l : Type} [Bot l] [Preorder l] {a b : Lpo l} : IsStronglyAtomic (TreeNode a b) where
  exists_covBy_le_of_lt := fun _ _ hlt ↦ match covBy_between hlt with | ⟨v, h₁, h₂, _⟩ => ⟨v, h₁, h₂⟩

lemma cov_by_iff {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} {t u : TreeNode a b} :
  t ⋖ u ↔ t.n + 1 = u.n ∧ Lpo.PermExt t.perm u.perm := by {
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
    (u : {u // t ⋖ u}) (x : ↑(a.rel.lev ⁻¹' {WithTop.some (t.n + 1)})) :
    ↑(b.rel.lev ⁻¹' {WithTop.some (t.n + 1)}) :=
  Subtype.mk (u.val.perm ⟨x.val, sorry⟩) (by {
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
    · sorry --rw [← hup _ hx, hvp _ hx]
    · by_cases hx' : x ∈ a.rel.lev ⁻¹' {WithTop.some (t.n + 1)}
      · have h := congrFun h ⟨x, hx'⟩; simp at h; sorry -- exact h
      · have h : x ∉ dom u := by
          simp [dom, Lpo.trunc, Lpo.nodes] at *
          intro hx''; apply hx'; rw [← hun] at hx''
          sorry
          --exact (Nat.succ_le_of_lt (hx hx'')).lt_iff_ne.mpr (Ne.symm hx')
        sorry
        -- rw [u.hdom _ h]; unfold dom at h; rw [← hun, hvn] at h
        -- rw [v.hdom _ h]
  · sorry

lemma finite_branching {l : Type} [Bot l] [PartialOrder l] (a b : Lpo l)
  (t : TreeNode a b) : { u | t ⋖ u }.Finite := by {
    refine @Finite.of_injective _ _ ?_ (covBy_injection t) (covBy_equiv _)
    sorry -- exact @Pi.finite _ _ (a.property.rel.fin_lev _) (fun _ => b.property.rel.fin_lev _)
  }

-- lemma perm_equivs_permute {l : Type} [Bot l] {n : ℕ} {p : Node → Node} {a : Lpo l} :
--     ∀ e ∈ perm_equivs n p a, ∀ e' ∈ perm_equivs n p a, (a.trunc n).val.permute e = (a.trunc n).val.permute e' := by
--   intro e he e' he'
--   have heq := fun x hx ↦ Eq.trans (Eq.symm (he x hx)) (he' x hx)
--   unfold Lpo.permute; refine lpo_eq_iff.mpr ⟨?_, ?_, ?_, ?_⟩
--   · exact Set.image_congr heq
--   · ext x y; sorry
--   · sorry
--   · sorry

lemma has_infinite_path {l : Type} [Preorder l] [OrderBot l] {a b : Lpo l}
    (hle : ∀ n, ∃ X : Set Node, ∃ e : (a.trunc n).nodes ≃ X,
      (a.trunc n).val.permute e ≤ b) : (Set.Ici (root a b)).Infinite := by {
    sorry
    -- have h : ∀ n, ∃ e : (a.trunc n).nodes ≃ X,
    --     (∀ x ∈ (a.trunc n).val.nodes, p x = e x) ∧
    --     (∀ x ∉ (a.trunc n).val.nodes, p x = default) ∧
    --     (a.trunc n).val.permute e ≤ b := by
    --   intro n; obtain ⟨e, he⟩ := hle n
    --   have h : ∀ x : Node, ∃ y, (x ∈ (a.trunc n).val.nodes → y = e x) ∧ (x ∉ (a.trunc n).val.nodes → y = default) := by
    --     intro x; by_cases hx : x ∈ (a.trunc n).val.nodes
    --     · use e x; simp [hx]
    --     · use default; simp [hx]
    --   choose p hp using h
    --   refine ⟨p, e, fun x hx ↦ (hp x).1 hx, fun x hx ↦ (hp x).2 hx, he⟩
    -- choose g hg using h
    -- let f (i : ℕ) : TreeNode a b := {
    --   n := i
    --   perm := g i
    --   hdom := by intro x hx; have ⟨_, _, h, _⟩ := hg i; exact h x hx
    --   heq := by obtain ⟨e, ⟨he, _⟩⟩ := hg i; exact ⟨e, fun x hx ↦ he x hx⟩
    --   le_b := by
    --     obtain ⟨e, he, _, hle⟩ := hg i; intro e' he'
    --     rw [perm_equivs_permute e' he' e he]; exact hle
    -- }
    -- have hsub : f '' Set.univ ⊆ Set.Ici (root a b) := by {
    --   simp [Set.Ici, f, Set.range]; intro i; refine ⟨bot_le, ?_⟩
    --   intro x hx; simp; sorry
    -- }
    -- refine Set.Infinite.mono hsub ?_
    -- refine Set.Infinite.image ?_ Set.infinite_univ
    -- simp [f]; intro i _ j _; simp; exact fun hij _ ↦ hij
  }

end TreeNode

open OmegaCompletePartialOrder

theorem pom_ge_iff_ge_fin {l : Type} [DCPO l] [OrderBot l] {p q : Pom l}
    (hle : ∀ n, p.trunc n ≤ q) : p ≤ q := by {
  -- Start with any arbitrary representatins of p and q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  unfold Pom.trunc at hle; simp only [Quotient.lift_mk] at hle
  have hle' : ∀ n, ∃ X : Set Node, ∃ e : (a.trunc n).val.nodes ≃ X,
      (a.trunc n).val.permute e ≤ b := by
    intro n; have ⟨a', ha', hlea⟩ := Pom.le_iff_2.mp (hle n) b rfl
    have ⟨e, he⟩ := Quotient.exact ha'
    refine ⟨a'.nodes, e, ?_⟩; rw [he]; exact hlea
  -- Invoke Konig's lemma to show that there is an infinitely increasing
  -- chain of permutations from a.trunc n to something smaller than b
  rcases exists_seq_covby_of_forall_covby_finite
          (TreeNode.finite_branching a b)
          (TreeNode.has_infinite_path hle') with ⟨f, h₀, hsucc⟩
  have hn (n : ℕ) : (f n).n = n := by
    induction n with
    | zero => rw [h₀]; rfl
    | succ n ih =>
      have ⟨hn, _⟩ := TreeNode.cov_by_iff.mp (hsucc n)
      refine hn.symm.trans ?_; rw [ih]
  have hf {i j} (hle : i ≤ j) : f i ≤ f j :=
    monotone_nat_of_le_succ (fun n ↦ (hsucc n).le) hle
  have hext {i j hi hj} (hle : i ≤ j) :
      Lpo.PermExt
        (Lpo.cast_perm (f i).perm hi (Y := (a.trunc i).nodes))
        (Lpo.cast_perm (f j).perm hj (Y := (a.trunc j).nodes)) := by
    constructor
    · intro x
      exact (hf hle).2.2 ⟨x, by rw [hn i]; exact Subtype.coe_prop _⟩
    · refine (congrArg₂ (· ⊆ ·) ?_ ?_).mp (hf hle).2.1
      · rw [hn i]
      · rw [hn j]
  -- Build a new chain by permuting truncations of a
  let c : Chain (Lpo l) := {
    toFun n := (a.trunc n).val.permute' (f n).perm (by rw [hn n]; rfl)
    monotone' := by
      intro i j hle
      refine Lpo.permute_monotone ?_ ?_
      · exact Lpo.trunc_mono (le_refl _) hle
      · exact hext hle
  }
  -- Witness that p ≤ q using the supremum of the new chain c as the
  -- representative lpo of p
  refine ⟨ωSup c, b, ?_, ?_, rfl⟩
  -- sup c is smaller than b, since every element of c is smaller than b
  · refine ωSup_le _ _ ?_; intro n; unfold c
    refine le_of_eq_of_le ?_ (f n).le_b
    refine (Lpo.permute'_eq ?_).symm; rw [hn n]
  -- a ≈ sup c
  · refine Quotient.eq_iff_equiv.mpr ?_
    refine Lpo.permute_chain ?_ ?_ (en := fun n ↦ Lpo.cast_perm (f n).perm ?_)
    · rw [hn n]
    · intro i; rfl
    · intro i j hle; exact hext hle
  }


noncomputable def pom_chain_to_lpo_chain {l : Type} [PartialOrder l] [OrderBot l]
    (c : Chain (Pom l)) : Chain (Lpo l) := {
  toFun n :=
    let rec go n : { α : Lpo l | c n = Quotient.mk' α } := match n with
    | Nat.zero => ⟨(c 0).out, (Quotient.out_eq _).symm⟩
    | Nat.succ n => by {
        have hle := c.monotone' (Nat.le_succ n)
        obtain ⟨α, h⟩ := go n
        have hex := Pom.le_iff_1.mp hle α h
        refine ⟨hex.choose, (Exists.choose_spec hex).1⟩
    }
    (go n).val
  monotone' := by
    intro i j hle
    generalize hk : j - i = k
    have hj : j = i + k := by sorry
    subst hj; induction k with
    | zero => exact le_refl _
    | succ k ih =>
        refine (ih ?_ ?_).trans ?_
        · simp only [le_add_iff_nonneg_right, zero_le]
        · simp only [add_tsub_cancel_left]
        · have : i + (k + 1) = Nat.succ (i + k) := by sorry
          rw [this]; simp; sorry
}

lemma pom_chain_to_lpo_chain_mem {l : Type} [DCPO l] [OrderBot l]
    (c : Chain (Pom l)) (i : ℕ) :
    c i = Quotient.mk' (pom_chain_to_lpo_chain c i) :=
  (pom_chain_to_lpo_chain.go c i).property

-- Inspired by Lemma D.4 from CONCUR'25
lemma lpo_chain_pom_chain_lub {l : Type} [DCPO l] [OrderBot l]
    {cl : Chain (Lpo l)} {cp : Chain (Pom l)}
    (h : ∀ i, cp i = Quotient.mk' (cl i)) (hc : ∀ x : l, ScottCompact x) :
    IsLUB (Set.range cp) (Quotient.mk' (ωSup cl)) := by
  constructor
  · intro p hp; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hp
    exact ⟨cl i, ωSup cl, le_ωSup _ _, h i, rfl⟩
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_setOf_eq]; intro p hp
    have h : ∀ n, ∃ β : Lpo l, (ωSup cl).trunc n ≤ β ∧ p = Quotient.mk _ β := by
      intro n
      let α := ωSup cl
      let N := { x ∈ α.nodes | α.rel.lev x ≤ n }
      have h : ∀ x : ↑N, ∃ i, x.val ∈ (cl i).nodes ∧ (α.trunc n).lab x = (cl i).lab x := by
        intro ⟨x, hx, hlev⟩
        have ⟨ℓ, h, hlab⟩ := hc (α.lab x) ((Chain.to_dSet cl).image _ (lab_monotone x))
          (by refine le_of_eq ?_; rfl)
        obtain ⟨β, hβ, rfl⟩ := (Set.mem_image _ _ _).mp h
        obtain ⟨i, rfl⟩ := Set.mem_range.mp hβ
        refine ⟨i, ?_⟩; sorry
      choose f hf using h
      have hN : N.Finite := by
        unfold N
        refine (congrArg _ ?_).mp
          (Set.finite_iUnion fun (k : Fin (n + 1)) ↦ α.property.rel.fin_lev k.val)
        ext x; simp only [Set.mem_iUnion, Set.mem_setOf_eq, exists_and_left]
        constructor
        · rintro ⟨hx, k, hlev⟩; refine ⟨hx, le_of_eq_of_le hlev ?_⟩
          simp [Nat.cast_lt, k.isLt]; sorry
        · intro ⟨hx, hlev⟩
          obtain ⟨k, hk⟩ := lev_finite hx
          refine ⟨hx, ⟨k, ?_⟩, hk⟩; sorry
      have hne : Nonempty ↑N := by
        obtain ⟨r, hr, hrl⟩ := α.property.rel.single_rooted
        refine ⟨r, hr, ?_⟩; exact le_of_eq_of_le (lev_root hr hrl) bot_le
      obtain ⟨k, hk⟩ := @Finite.exists_max _ _ hN hne _ f
      obtain ⟨β, rfl, hle⟩ := Pom.le_iff_1.1 (hp (f k)) (cl (f k)) (h _)
      refine ⟨β, le_trans ?_ hle, rfl⟩
      have htr := α.trunc_le n
      have hno : N = (α.trunc n).nodes := sorry
      constructor
      · intro x hx; sorry
      · intro x hx y hxy; sorry
      · intro x hx y hy; sorry
      · intro x; sorry
      · intro x hx; sorry
      · intro x hx; sorry
    choose f hf using h
    refine pom_ge_iff_ge_fin ?_
    intro n; refine ⟨(ωSup cl).trunc n, f n, (hf n).1, ?_, (hf n).2⟩
    simp only [Pom.trunc, Quotient.lift_mk]
    sorry

lemma pom_chain_to_lpo_chain_lub {l : Type} [DCPO l] [OrderBot l]
    (c : Chain (Pom l)) (hc : ∀ x : l, ScottCompact x) :
    IsLUB (Set.range c) (Quotient.mk' (ωSup (pom_chain_to_lpo_chain c))) :=
  lpo_chain_pom_chain_lub (pom_chain_to_lpo_chain_mem c) hc

def lpo_chain_to_pom {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Lpo l)) :
    Chain (Pom l) := {
  toFun n := Quotient.mk _ (c n)
  monotone' i j hle := ⟨c i, c j, c.monotone' hle, rfl, rfl⟩
}
lemma lpo_chain_to_pom_lub {l : Type} [DCPO l] [OrderBot l]
    (c : Chain (Lpo l)) (h : ∀ x : l, ScottCompact x) :
    IsLUB (Set.range (lpo_chain_to_pom c)) (Quotient.mk _ (ωSup c)) :=
  lpo_chain_pom_chain_lub (fun _ ↦ rfl) h

instance {l : Type} [DCPO l] [OrderBot l] (hc : ∀ x : l, ScottCompact x) :
    OmegaCompletePartialOrder (Pom l) where
  ωSup c := Quotient.mk' (ωSup (pom_chain_to_lpo_chain c))
  le_ωSup c i := by
    refine (pom_chain_to_lpo_chain_lub c hc).1 ?_
    exact Set.mem_range.mpr ⟨i, rfl⟩
  ωSup_le c p h := by
    refine (pom_chain_to_lpo_chain_lub c hc).2 ?_
    intro q hq; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hq; exact h i

-- lemma dset_to_chain {l : Type} [LE l] (d : DSet (Pom l)) :
--     ∃ c : OmegaCompletePartialOrder.Chain (Pom l),
--       c.to_dSet.dSup
-- STRATEGY
--  1. If we truncate every element in the directed set to level n,
--     then there are only finitely many element
--  2. Let c i := an upper bound of all those truncated elements
--  3. Since Pom is ω-complete, we can get the sup of that chain
--  4.

-- instance {l : Type} [DCPO l] [OrderBot l] : DCPO (Pom l) where
--   dSup d := sorry
