import Mathlib.Data.Finite.Prod
import Mathlib.Data.Fintype.Lattice
import Mathlib.Data.Prod.Basic
import Mathlib.Order.Atoms
import Mathlib.Order.KonigLemma

import Pcol.Semantics.Pom.Order
import Pcol.Semantics.Lpo.FinApprox

def Pomfin (l : Type) [Bot l] : Type := Quotient (@Lpofin.instSetoid l _)

namespace Pomfin

def to_pom {l : Type} [Bot l] (p : Pomfin l) : Pom l :=
  p.lift
    (fun a => Quotient.mk' a.val)
    (fun _ _ heq => Quotient.sound heq)

instance {l : Type} [Bot l] : Coe (Pomfin l) (Pom l) where
  coe := Pomfin.to_pom

instance {l : Type} [LE l] [Bot l] : LE (Pomfin l) where
  le p q := p.to_pom ≤ q.to_pom

instance {l : Type} [PartialOrder l] [OrderBot l] : PartialOrder (Pomfin l) where
  le_trans p q r hpq hqr := sorry
  le_refl := sorry
  le_antisymm := sorry

lemma to_pom_mono {l : Type} [PartialOrder l] [OrderBot l] :
    Monotone (@Pomfin.to_pom l _) := fun _ _ hle ↦ hle

lemma val_mem_to_pom {l : Type} [Bot l] {α : Lpofin l} {p : Pomfin l} (h : Quotient.mk' α = p) :
    α.val ∈ p.to_pom := by
  rw [← h]; rfl

end Pomfin

namespace Pom

noncomputable def trunc {l : Type} [Preorder l] [OrderBot l] (p : Pom l) (n : ℕ) : Pomfin l :=
  p.lift
    (fun (a : Lpo l) ↦ Quotient.mk (@Lpofin.instSetoid l _) (a.trunc n))
    (fun _ _ h ↦ Quotient.eq_iff_equiv.2 (Lpo.trunc_equiv h))

lemma trunc_mono {l : Type} [PartialOrder l] [OrderBot l] {p q : Pom l} {n m : ℕ}
    (hp : p ≤ q) (hn : n ≤ m) : p.trunc n ≤ q.trunc m := by
  obtain ⟨α, rfl, β, rfl, hle⟩ := hp
  refine ⟨α.trunc n, rfl, β.trunc m, rfl, Lpo.trunc_mono hle hn⟩

lemma trunc_le {l : Type} [PartialOrder l] [OrderBot l] (p : Pom l) (n : ℕ) :
    p.trunc n ≤ p := by
  obtain ⟨α, rfl⟩ := p.exists_rep
  refine ⟨α.trunc n, rfl, α, rfl, Lpo.trunc_le _ _⟩

lemma lpo_trunc_mem {l : Type} [Preorder l] [OrderBot l] {α : Lpo l} {p : Pom l} {n : ℕ} (h : α ∈ p) :
    Quotient.mk' (α.trunc n) = p.trunc n := by
  rw [h]; rfl

end Pom

private structure TreeNode {l : Type} [Bot l] [LE l] (a b : Lpo l) : Type where
  n : ℕ
  X : Set Node
  -- Perm is a permutation
  perm : (a.trunc n).nodes ≃ X
  le_b : (a.trunc n).val.permute perm ≤ b

attribute [ext] TreeNode

namespace TreeNode

def dom {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  (a.trunc t.n).val.nodes

def range {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Set Node :=
  t.X

noncomputable def root {l : Type} [LE l] [OrderBot l] (a b : Lpo l) : TreeNode a b :=
  let x := a.property.rel.single_rooted.choose
  let y := b.property.rel.single_rooted.choose
  {
    n := 0
    X := {y}
    perm := {
      toFun _ := ⟨y, Set.mem_singleton _⟩
      invFun _ := ⟨x, by {
        have ⟨hx, hroot⟩ := Classical.choose_spec a.property.rel.single_rooted
        refine ⟨hx, le_of_eq ?_⟩; exact lev_root hx hroot
      }⟩
      left_inv z := by
        have ⟨hx, hroot⟩ := Classical.choose_spec a.property.rel.single_rooted
        ext; simp only
        refine not_not.mp ((hroot _ z.property.1).mt ?_); intro hrel
        have :=
          lt_of_eq_of_lt (lev_root hx hroot).symm
            (lt_of_lt_of_le (lev_mono hrel) z.property.2)
        simp only [Nat.cast_zero, lt_self_iff_false] at this
      right_inv z := by ext; symm; exact Set.mem_singleton_iff.mp z.property
    }
    le_b := by
      simp only [Lpo.trunc, Lpo.trunc_base, Lpo.permute]; constructor
      · simp only [Lpo.nodes, Set.singleton_subset_iff]
        exact b.property.rel.single_rooted.choose_spec.1
      · simp only [Rel.is_down_closed, Lpo.nodes, Set.mem_singleton_iff, forall_eq]
        intro z hrel; by_contra hne
        have ⟨hz, hy⟩ := b.property.rel_dom hrel
        have := b.property.rel.single_rooted.choose_spec.2 _ hz (Ne.symm hne)
        exact hne (b.property.rel.antisymm hrel this)
      · simp only [Lpo.nodes, Set.mem_singleton_iff, Lpo.rel, Nat.cast_zero, ENat.not_lt_zero,
          nonpos_iff_eq_zero, Set.mem_setOf_eq, Set.coe_setOf, Equiv.coe_fn_symm_mk, and_self,
          exists_and_left, exists_prop, eq_iff_iff, forall_eq, true_and]
        constructor
        · intro ⟨hrel, _⟩; exfalso; exact a.property.rel.irrefl _ hrel
        · intro hrel; exfalso; exact b.property.rel.irrefl _ hrel
      · simp only [Lpo.lab, Set.mem_singleton_iff, Nat.cast_zero, ENat.not_lt_zero,
          nonpos_iff_eq_zero, Equiv.coe_fn_symm_mk, ↓reduceIte, dite_eq_ite, ite_self]
        intro z; exact bot_le
      · simp only [Lpo.nodes, Set.mem_singleton_iff, Lpo.form, Nat.cast_zero, ENat.not_lt_zero,
          nonpos_iff_eq_zero, Set.mem_setOf_eq, Set.coe_setOf, Equiv.coe_fn_symm_mk, exists_and_left,
          Subtype.exists, exists_prop, exists_eq_left, forall_eq, true_and]
        sorry
      · simp only [Lpo.nodes, Set.mem_singleton_iff, Lpo.bots, Lpo.lab, Lpo.rel, Nat.cast_zero,
        ENat.not_lt_zero, nonpos_iff_eq_zero, Set.mem_setOf_eq, Set.coe_setOf, Equiv.coe_fn_symm_mk,
        ↓reduceIte, dite_eq_ite, ite_self, and_true, Set.setOf_eq_eq_singleton, exists_eq_left]
        intro z hz; by_cases heq : z = y
        · left; exact heq
        · right; exact b.property.rel.single_rooted.choose_spec.2 _ hz (Ne.symm heq)
  }

instance {l : Type} [LE l] [Bot l] {a b : Lpo l} : LE (TreeNode a b) where
  le t u :=
    t.n ≤ u.n ∧
    Lpo.PermExt t.perm u.perm

instance {l : Type} [LE l] [Bot l] {a b: Lpo l} : Preorder (TreeNode a b) where
  le_refl t := by
    refine ⟨le_refl _, ⟨le_refl _, ?_⟩⟩
    · intro x; rfl
  le_trans t u v := by
    intro ⟨hn₁, ⟨hno₁, hp₁⟩⟩ ⟨hn₂, ⟨hno₂, hp₂⟩⟩
    refine ⟨le_trans hn₁ hn₂, ⟨le_trans hno₁ hno₂, ?_⟩⟩
    intro x; exact (hp₁ x).trans (hp₂ _)

instance {l : Type} [LE l] [Bot l] {a b : Lpo l} : PartialOrder (TreeNode a b) where
  le_antisymm t u := by
    intro ⟨hn₁, hex₁⟩ ⟨hn₂, hex₂⟩
    have hn := le_antisymm hn₁ hn₂; ext1
    · exact hn
    · ext x; constructor <;> intro hx
      · have := hex₁.extend (t.perm.symm ⟨_, hx⟩)
        simp only [Equiv.apply_symm_apply] at this; rw [this]
        exact Subtype.coe_prop _
      · have := hex₂.extend (u.perm.symm ⟨_, hx⟩)
        simp only [Equiv.apply_symm_apply] at this; rw [this]
        exact Subtype.coe_prop _
    · refine heq_of_cast_eq ?_ ?_
      · rw [hn]; have := le_antisymm hex₁.cod_sub hex₂.cod_sub; rw [this]
      · ext x; refine Eq.trans ?_ (hex₂.extend x).symm
        -- refine congrArg Subtype.val ?_ -- (congr ?_ ?_))
        -- have {h} : cast h t.perm = t.perm := cast_eq _ _
        -- rw [this _]
        sorry


lemma le_and_n_eq {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hle : t ≤ u) (hn : t.n = u.n) : t = u := by
  refine le_antisymm hle ⟨?_, ⟨?_, ?_⟩⟩
  · exact le_of_eq hn.symm
  · exact (Lpo.trunc_mono (le_refl a) (le_of_eq hn.symm)).nodes
  · intro x; exact (hle.2.extend ⟨x, _⟩).symm

lemma lt_iff {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b} :
  t < u ↔ t.n < u.n ∧ Lpo.PermExt t.perm u.perm := by
    constructor
    · intro ⟨⟨hn, hex⟩, hc⟩; refine ⟨?_, hex⟩
      · refine Nat.lt_iff_le_and_not_ge.2 ⟨hn, fun h => hc ?_⟩
        cases Nat.lt_or_eq_of_le hn with
        | inl hlt => apply Nat.not_lt_of_le at h; contradiction
        | inr heq => exact le_of_eq (Eq.symm (le_and_n_eq ⟨hn, hex⟩ heq))
    · intro ⟨hn, hex⟩; refine ⟨⟨Nat.le_of_lt hn, hex⟩, fun hc => ?_⟩
      have h := hc.1; linarith

def cover_of {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : TreeNode a b :=
have hle := Lpo.trunc_mono (le_refl a) (Nat.succ_le_of_lt (lt_iff.mp hlt).1)
{
  n := t.n + 1
  X := _
  perm := Lpo.perm_subset u.perm hle.nodes
  le_b := by
    refine le_trans ?_ u.le_b
    exact Lpo.permute_monotone hle Lpo.perm_subset_ext
}

lemma cover_is_cover {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : t ⋖ cover_of hlt := by
  refine ⟨lt_iff.mpr ⟨?_, ?_, ?_⟩, ?_⟩
  · exact Nat.lt_succ_self _
  · refine (Lpo.trunc_mono (le_refl _) ?_).nodes; exact Nat.le_succ _
  · intro x; refine ((le_of_lt hlt).2.2 x).trans ?_
    symm; simp only [cover_of]; exact Lpo.perm_subset_ext.2 _
  · intro v htv hc
    have h₁ := (lt_iff.mp htv).1
    have h₂ := (lt_iff.mp hc).1; simp only [cover_of] at h₂
    linarith

lemma cover_le {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b}
    (hlt : t < u) : cover_of hlt ≤ u := by
  unfold cover_of; constructor
  · exact Nat.succ_le_of_lt (lt_iff.mp hlt).1
  · simp only; exact Lpo.perm_subset_ext

instance {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} : IsStronglyAtomic (TreeNode a b) where
  exists_covBy_le_of_lt _ _ hlt := ⟨cover_of hlt, cover_is_cover hlt, cover_le hlt⟩

lemma cov_by_iff {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} {t u : TreeNode a b} :
  t ⋖ u ↔ t.n + 1 = u.n ∧ Lpo.PermExt t.perm u.perm := by
  constructor
  · intro ⟨hlt, hnlt⟩; constructor
    · refine le_antisymm ?_ ?_
      · exact Nat.succ_le_of_lt (lt_iff.mp hlt).1
      · refine le_of_not_lt fun hc ↦ ?_
        have := lt_iff.mpr.mt (hnlt (cover_is_cover hlt).1)
        simp only [not_and, cover_of] at this
        refine this hc Lpo.perm_subset_ext
    · have ⟨⟨_, hf⟩, _⟩ := hlt; exact hf
  · intro ⟨hn, hp⟩; refine ⟨lt_iff.mpr ⟨by linarith, hp⟩, ?_⟩
    · intro v hv hu
      have hn₁ := (lt_iff.mp hv).1
      have hn₂ := (lt_iff.mp hu).1
      linarith

def covBy_injection {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} (t : TreeNode a b)
    (u : {u // t ⋖ u})
    (x : { x // x ∈ a.nodes ∧  a.rel.lev x ≤ t.n + 1 }) :
    { x // x ∈ b.nodes ∧ b.rel.lev x ≤ t.n + 1} :=
  ⟨u.val.perm ⟨x.val, by {
    have := (cov_by_iff.mp u.property).1; rw [← this]; exact x.property
  }⟩, by {
    constructor
    · refine u.val.le_b.nodes ?_; exact Subtype.coe_prop _
    · refine le_of_eq_of_le ?_ x.property.2
      refine (lev_isotone u.val.le_b (Subtype.coe_prop _)).symm.trans ?_
      refine (Lpo.permute_lev _ _).symm.trans ?_
      refine lev_isotone (Lpo.trunc_le a u.val.n) ?_
      have := (cov_by_iff.mp u.property).1; rw [← this]; exact x.property
  }⟩

lemma covBy_injective {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l} (t : TreeNode a b) :
    Function.Injective (covBy_injection t) := by
  intro ⟨u, hu⟩ ⟨v, hv⟩ h
  unfold covBy_injection at h; simp only at h
  have ⟨hun, hup⟩ := cov_by_iff.mp hu
  have ⟨hvn, hvp⟩ := cov_by_iff.mp hv
  ext x <;> simp only
  · rw [← hun, ← hvn]
  · constructor <;> intro hx
    · let y := (v.perm ⟨u.perm.symm ⟨_, hx⟩, by {rw [← hvn, hun]; exact Subtype.coe_prop _}⟩)
      have : x = y.val := by
        have : x = (Subtype.mk x hx).val := rfl; rw [this]
        refine (congrArg _ (Equiv.apply_symm_apply u.perm _).symm).trans ?_
        sorry
      rw [this]; exact y.property
    · sorry
  · sorry

lemma finite_branching {l : Type} [PartialOrder l] [OrderBot l] (a b : Lpo l)
    (t : TreeNode a b) : { u | t ⋖ u }.Finite := by
  let f (u : { u | t ⋖ u }) : (a.trunc u.val.n).nodes ≃ u.val.X := u.val.perm
  refine @Finite.of_injective _ _ ?_ (covBy_injection t) (covBy_injective t)
  exact @Pi.finite _ _ (a.trunc (t.n + 1)).property (fun _ => (b.trunc (t.n + 1)).property)

lemma has_infinite_nodes {l : Type} [PartialOrder l] [OrderBot l] {a b : Lpo l}
    (hle : ∀ n, (Pom.mk a).trunc n ≤ Pom.mk b) :
    (Set.Ici (root a b)).Infinite := by
  have h n : ∃ t : TreeNode a b, t.n = n ∧ root a b ≤ t := by
    have ⟨a', ha', hlea⟩ := Pom.ge_lpo (hle n)
    have ⟨e, he⟩ := Quotient.exact ha'
    refine ⟨⟨n, a'.nodes, e, ?_⟩, rfl, ⟨bot_le, ?_, ?_⟩⟩
    · exact le_of_eq_of_le he hlea
    · intro x hx; exact (Lpo.trunc_mono (le_refl _) bot_le).nodes hx
    · intro x; simp [root]; sorry
  choose f hf using h
  refine (Set.infinite_univ.image ?_ (f := f)).mono ?_
  · intro i _ j _ heq;
    refine (hf i).1.symm.trans ?_; rw [heq]; exact (hf j).1
  · intro t ht; obtain ⟨n, _, rfl⟩ := (Set.mem_image _ _ _).mp ht
    exact (hf n).2

end TreeNode

open OmegaCompletePartialOrder

theorem pom_ge_iff_ge_fin {l : Type} [DCPO l] [OrderBot l] {p q : Pom l}
    (hle : ∀ n, p.trunc n ≤ q) : p ≤ q := by {
  -- Start with any arbitrary representations of p and q
  obtain ⟨a, rfl⟩ := Quotient.exists_rep p
  obtain ⟨b, rfl⟩ := Quotient.exists_rep q
  -- Invoke Konig's lemma to show that there is an infinitely increasing
  -- chain of permutations from a.trunc n to something smaller than b
  obtain ⟨f, h₀, hsucc⟩ :=
    exists_seq_covby_of_forall_covby_finite
      (TreeNode.finite_branching a b)
      (TreeNode.has_infinite_nodes hle)
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
  -- Build a new chain by permuting truncations
  let c : Chain (Lpo l) := {
    toFun n := (a.trunc n).val.permute' (f n).perm (by rw [hn n]; rfl)
    monotone' i j hle := by
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

namespace Pom

noncomputable def ext {X : Type} [OmegaCompletePartialOrder X]
    (f : Pomfin l → X) (hf : Monotone f) (p : Pom l) : X :=
  ωSup {
    toFun n := f (p.trunc n)
    monotone' _ _ hle := hf (trunc_mono (le_refl _) hle)
  }

lemma upper_bound_of_compact_pom (c : Chain (Pom l)) (n : ℕ) :
    ∃ i, (ωSup c).trunc n ≤ (c i).trunc n := by
  have ⟨c', hc⟩ := exists_lpo_chain_of_pom_chain c
  have ⟨i, hle⟩ := upper_bound_of_compact c' n
  refine ⟨i, (ωSup c').trunc n, ?_, (c' i).trunc n, ?_, ?_⟩
  · refine Pomfin.val_mem_to_pom (lpo_trunc_mem ?_)
    have ⟨hle, hge⟩ := lpo_chain_pom_chain_lub hc
    simp only [upperBounds, Set.mem_range, forall_exists_index, forall_apply_eq_imp_iff,
      Set.mem_setOf_eq, lowerBounds] at hle hge
    refine le_antisymm ?_ ?_
    · exact ωSup_le _ _ hle
    · exact hge (le_ωSup _)
  · exact Pomfin.val_mem_to_pom (lpo_trunc_mem (hc i))
  · exact Lpo.trunc_le_trunc hle

theorem ext_continuous {X : Type} [OmegaCompletePartialOrder X] {f : Pomfin l → X}
    (hf : Monotone f) : ωScottContinuous (ext _ hf) := by
  refine ωScottContinuous.of_monotone_map_ωSup ⟨?_, ?_⟩
  · intro p q hle; refine ωSup_le_ωSup_of_le ?_
    intro n; use n; exact hf (trunc_mono hle (le_refl _))
  · intro c; unfold ext; refine le_antisymm ?_ ?_
    · refine ωSup_le _ _ ?_; intro n
      have ⟨i, hi⟩ := upper_bound_of_compact_pom c n
      refine (hf hi).trans (le_trans ?_ (le_ωSup _ i))
      refine le_of_eq_of_le ?_ (le_ωSup _ n); rfl
    · refine ωSup_le _ _ ?_; intro i
      refine ωSup_le _ _ ?_; intro n
      refine le_trans ?_ (le_ωSup _ n)
      exact hf (trunc_mono (le_ωSup _ i) (le_refl _))

end Pom
