import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.KonigLemma

import Pcol.Semantics.Pom.Order
import Pcol.Semantics.Lpo.FinApprox

def Pomfin (l : Type) [Bot l] : Type := Quotient (@Lpofin.instSetoid l _)

instance {l : Type} [Bot l] : Coe (Pomfin l) (Pom l) where
  coe p := p.lift
    (fun a => Quotient.mk' a.val)
    (fun _ _ heq => Quotient.sound heq)

namespace Pom

noncomputable def trunc {l : Type} [Preorder l] [OrderBot l] (p : Pom l) (n : ℕ) : Pomfin l :=
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
  -- Start with any arbitrary representations of p and q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  unfold Pom.trunc at hle; simp only [Quotient.lift_mk] at hle
  have hle' : ∀ n, ∃ X : Set Node, ∃ e : (a.trunc n).val.nodes ≃ X,
      (a.trunc n).val.permute e ≤ b := by
    intro n; have ⟨a', ha', hlea⟩ := Pom.ge_lpo (hle n)
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
  refine ⟨ωSup c, ?_, b, rfl, ?_⟩
  -- a ≈ sup c
  · refine Quotient.eq_iff_equiv.mpr ?_
    refine Lpo.permute_chain ?_ ?_ (en := fun n ↦ Lpo.cast_perm (f n).perm ?_)
    · rw [hn n]
    · intro i; rfl
    · intro i j hle; exact hext hle
  -- sup c is smaller than b, since every element of c is smaller than b
  · refine ωSup_le _ _ ?_; intro n; unfold c
    refine le_of_eq_of_le ?_ (f n).le_b
    refine (Lpo.permute'_eq ?_).symm; rw [hn n]
  }

open Cardinal

def LpoChain (l : Type) [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) (n : ℕ) :=
  { f : Fin n → Lpo l //
    Monotone f ∧ ∀ k, (f k).nodes.compl.Infinite ∧ f k ∈ c k }

namespace LpoChain

lemma exists_extensible_perm {X Y : Set Node} (hinf : X.compl.Infinite) (hsub : X ⊆ Y) :
    ∃ Z : Set Node, ∃ e : Y ≃ Z, Z.compl.Infinite ∧ Lpo.PermExt (Equiv.refl X) e := by
  have hc : Cardinal.mk X.compl = Cardinal.mk (Bool × Node) := by
    refine Eq.trans ?_ (Eq.symm ?_) (b := ℵ₀)
    · exact @Cardinal.mk_eq_aleph0 _ _ hinf.to_subtype
    · exact Cardinal.mk_eq_aleph0 _
  have ⟨e⟩ := Cardinal.eq.mp hc
  -- U witnesses the permutation of the remaining available nodes into two countably infinite
  -- sets of nodes, one which can be used now and the other to be left available
  let U i : Set Node := Subtype.val ∘ e.symm '' Set.prod {i} Set.univ
  have hU i : (U i).Infinite := by
    unfold U; refine Set.Infinite.image ?_ ?_
    · exact Set.injOn_of_injective (Subtype.val_injective.comp e.symm.injective)
    · exact Set.Infinite.prod_right Set.infinite_univ (Set.singleton_nonempty _)
  have hd i : Disjoint X (U i) := by
    refine Set.subset_compl_iff_disjoint_left.mp ?_
    unfold U; simp only [Set.image, Function.comp]
    rintro _ ⟨x, _, rfl⟩; exact Subtype.coe_prop _
  have hc : Cardinal.mk ↑(Y \ X) ≤ Cardinal.mk (U true) := by
    refine le_of_le_of_eq Cardinal.mk_le_aleph0 ?_
    exact (@Cardinal.mk_eq_aleph0 _ _ (hU _).to_subtype).symm
  obtain ⟨Z, hZ, e', hext⟩ :=
    Lpo.perm_extend_to (U true) (Equiv.refl X) hsub (hd true) hc
  refine ⟨X ∪ Z, e', ?_, hext⟩
  refine Set.Infinite.mono ?_ (hU false)
  refine Set.subset_compl_iff_disjoint_left.mpr (Disjoint.union_left ?_ ?_)
  · exact hd false
  · refine Disjoint.mono_left hZ ?_
    refine (Set.disjoint_image_iff ?_).mpr ?_
    · exact Subtype.val_injective.comp e.symm.injective
    · refine Set.disjoint_prod.mpr (Or.inl ?_)
      refine Set.disjoint_singleton.mpr ?_
      simp only [ne_eq, Bool.true_eq_false, not_false_eq_true]

lemma exists_extension {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) (n : ℕ)
    (lc : LpoChain l c n) : ∃ lc' : LpoChain l c (n + 1), ∀ k : Fin n, lc.val k = lc'.val k := by
  match n with
  | Nat.zero =>
    have ⟨α, heq⟩ := (c 0).exists_rep
    obtain ⟨Y, e, hY, he⟩ :=
      exists_extensible_perm Set.finite_empty.infinite_compl bot_le (Y := α.nodes)
    use {
      val := fun _ ↦ α.permute e
      property := by
        refine ⟨?_, fun n ↦ ⟨?_, ?_⟩⟩
        · intro _ _ _; exact le_refl _
        · simp only [Lpo.permute, Lpo.nodes]; exact hY
        · have := n.fin_one_eq_zero; subst this
          exact heq.symm.trans (Quotient.eq_iff_equiv.mpr ⟨e, rfl⟩)
    }
    intro n; exact Fin.elim0 n
  | Nat.succ n =>
    have hle := c.monotone' (Nat.le_succ n)
    have ⟨hinf, hc⟩ := lc.property.2 ⟨n, Nat.lt_succ_self _⟩
    have ⟨β, hβ, hle⟩ := Pom.le_lpo hinf (le_of_eq_of_le hc.symm hle)
    obtain ⟨Y, e, hY, he⟩ :=
      exists_extensible_perm hinf hle.nodes
    use {
      val := fun k ↦ if hk : k.val < n.succ then lc.val ⟨k.val, hk⟩ else β.permute e
      property := by
        refine ⟨fun i j hij ↦ ?_, fun j ↦ ⟨?_, ?_⟩⟩ <;>
          by_cases hj : j.val < n.succ <;> simp only [hj, ↓reduceDIte]
        · have hi := lt_of_le_of_lt (Fin.val_fin_le.mpr hij) hj
          rw [dif_pos hi]; exact lc.property.1 hij
        · by_cases hi : i.val < n.succ
          · rw [dif_pos hi]
            have := le_of_eq_of_le (Lpo.permute_refl _).symm (Lpo.permute_monotone hle he)
            refine (lc.property.1 ?_).trans this
            simp only [Nat.succ_eq_add_one, Fin.mk_le_mk, Nat.le_of_lt_succ hi]
          · rw [dif_neg hi]
        · exact (lc.property.2 ⟨j, hj⟩).1
        · exact hY
        · exact (lc.property.2 ⟨j, hj⟩).2
        · have := eq_of_le_of_not_lt (Nat.le_of_lt_succ j.isLt) hj; rw [this]
          exact hβ.trans (Quotient.eq_iff_equiv.mpr ⟨e, rfl⟩)
    }
    intro k; simp only [Nat.succ_eq_add_one, Fin.coe_eq_castSucc, Fin.coe_castSucc, Fin.is_lt,
      ↓reduceDIte, Fin.eta]

def empty {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} : LpoChain l c 0 := {
  val := Fin.elim0
  property := by refine ⟨?_, ?_⟩; all_goals { intro n ; exfalso ; exact Fin.elim0 n }
}

lemma monotone {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} {n : ℕ}
    {i j : Fin n} {lc : LpoChain l c n} (hle : i ≤ j) : lc.val i ≤ lc.val j := lc.property.1 hle

lemma mem_pom {l : Type} [PartialOrder l] [OrderBot l] {c : Chain (Pom l)} {n : ℕ}
    (i : Fin n) {lc : LpoChain l c n} : lc.val i ∈ c i := (lc.property.2 i).2

end LpoChain

lemma exists_lpo_chain_of_pom_chain {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Pom l)) :
    ∃ c' : Chain (Lpo l), ∀ i, c' i ∈ c i := by
  choose f hf using LpoChain.exists_extension c
  let ch n : LpoChain l c n := Nat.rec LpoChain.empty f n
  use {
    toFun n := (ch (n+1)).val ⟨n, Nat.lt_succ_self _⟩
    monotone' := by
      refine monotone_nat_of_le_succ ?_
      intro n; unfold ch
      refine le_of_eq_of_le (hf _ _ _) (LpoChain.monotone ?_)
      refine Fin.le_iff_val_le_val.mpr ?_; simp only [Fin.val_natCast]
      refine le_of_eq_of_le (Nat.mod_eq_of_lt ?_) (Nat.le_succ _)
      linarith
  }
  intro n
  simp only [ch, DFunLike.coe]
  exact LpoChain.mem_pom (l := l) ⟨n, Nat.lt_succ_self _⟩

variable {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]

lemma upper_bound_of_compact (c : Chain (Lpo l)) (n : ℕ) :
    ∃ i, (ωSup c).trunc n ≤ c i := by
  let X := ((ωSup c).trunc n).nodes
  have h : ∀ x : ↑X, ∃ i : ℕ,
      x.val ∈ (c i).nodes ∧ ((ωSup c).trunc n).lab x ≤ (c i).lab x := by
    intro ⟨x, hx, hlev⟩
    simp only [Lpo.ωSup_nodes, Set.mem_iUnion] at hx
    obtain ⟨i, hx⟩ := hx
    have ⟨ℓ, h, hlab⟩ :=
      ScottCompact.scottCompact ((ωSup c).lab x)
        ((Chain.to_dSet c).image _ (lab_monotone x))
        (by refine le_of_eq ?_; rfl)
    obtain ⟨β, hβ, rfl⟩ := (Set.mem_image _ _ _).mp h
    obtain ⟨j, rfl⟩ := Set.mem_range.mp hβ
    refine ⟨max i j, ?_, ?_⟩
    · exact (c.monotone' le_sup_left).nodes hx
    · exact
        ((Lpo.trunc_le _ _).lab _).trans
          (hlab.trans
            ((c.monotone' le_sup_right).lab _))
  choose f hf using h
  have hne : Nonempty ↑X := by
    obtain ⟨r, hr, hrl⟩ := (ωSup c).property.rel.single_rooted
    refine ⟨r, hr, ?_⟩; exact le_of_eq_of_le (lev_root hr hrl) bot_le
  obtain ⟨k, hk⟩ := @Finite.exists_max _ _ ((ωSup c).trunc n).property hne _ f
  refine ⟨f k, ?_⟩
  have hnodes : X ⊆ (c (f k)).nodes := by
    intro x hx; exact (c.monotone' (hk _)).nodes (hf ⟨x, hx⟩).1
  constructor
  · exact hnodes
  · intro x hx y hrel; refine (Lpo.trunc_le _ _).downcl x hx y ?_
    exact le_rel (le_ωSup _ _) hrel
  · intro x hx y hy
    exact
      ((Lpo.trunc_le _ _).rel _ hx _ hy).trans
        ((le_ωSup c _).rel _ (hnodes hx) _ (hnodes hy)).symm
  · intro x; by_cases hx : x ∈ X
    · exact (hf ⟨x, hx⟩).2.trans ((c.monotone' (hk ⟨x, hx⟩)).lab x)
    · refine le_of_eq_of_le ?_ bot_le
      exact ((ωSup c).trunc n).val.property.lab_dom _ hx
  · intro x hx;
    refine ((Lpo.trunc_le (ωSup c) n).form x hx).trans ?_
    exact ((le_ωSup c _).form _ (hnodes hx)).symm
  · intro x hx
    rcases (Lpo.trunc_le _ n).succ _ ((le_ωSup c _).nodes hx) with
        hx' | ⟨z, hbot, hrel⟩
    · left; exact hx'
    · right; refine ⟨z, hbot, ?_⟩
      refine ((le_ωSup c _).rel _ ?_ _ hx).mpr hrel
      exact (le_ωSup c _).downcl _ hx _ hrel

-- Inspired by Lemma D.4 from CONCUR'25
lemma lpo_chain_pom_chain_lub
    {cl : Chain (Lpo l)} {cp : Chain (Pom l)}
    (h : ∀ i, cl i ∈ cp i) :
    IsLUB (Set.range cp) (Quotient.mk' (ωSup cl)) := by
  constructor
  · intro p hp; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hp
    exact ⟨cl i, h i, ωSup cl, rfl, le_ωSup _ _⟩
  · simp only [lowerBounds, upperBounds, Set.mem_range, forall_exists_index,
      forall_apply_eq_imp_iff, Set.mem_setOf_eq]; intro p hp
    refine pom_ge_iff_ge_fin ?_; intro n
    simp [Pom.trunc]
    conv => lhs; rhs; exact Quotient.lift_mk _ _ _
    obtain ⟨i, hi⟩ :=  upper_bound_of_compact cl n
    refine le_trans ⟨(ωSup cl).trunc n, ?_, cl i, h i, hi⟩ (hp i)
    refine Quotient.eq_iff_equiv.mpr ?_; rfl

def lpo_chain_to_pom {l : Type} [PartialOrder l] [OrderBot l] (c : Chain (Lpo l)) :
    Chain (Pom l) := {
  toFun n := Quotient.mk _ (c n)
  monotone' i j hle := ⟨c i, rfl, c j, rfl, c.monotone' hle⟩
}
lemma lpo_chain_to_pom_lub {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]
    (c : Chain (Lpo l)) :
    IsLUB (Set.range (lpo_chain_to_pom c)) (Quotient.mk _ (ωSup c)) :=
  lpo_chain_pom_chain_lub (fun _ ↦ rfl)

instance {l : Type} [DCPO l] [OrderBot l] [ScottCompact l] :
    OmegaCompletePartialOrder (Pom l) where
  ωSup c := Quotient.mk' (ωSup (exists_lpo_chain_of_pom_chain c).choose)
  le_ωSup c i := by
    refine (lpo_chain_pom_chain_lub (exists_lpo_chain_of_pom_chain c).choose_spec).1 ?_
    exact Set.mem_range.mpr ⟨i, rfl⟩
  ωSup_le c p h := by
    refine (lpo_chain_pom_chain_lub (exists_lpo_chain_of_pom_chain c).choose_spec).2 ?_
    intro q hq; obtain ⟨i, rfl⟩ := Set.mem_range.mpr hq; exact h i
