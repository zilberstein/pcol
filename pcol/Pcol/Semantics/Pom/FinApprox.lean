import Mathlib
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
    (fun (a : Lpo l) => Quotient.mk (@Lpofin.instSetoid l _) (a.trunc n))
    (fun _ _ h => Quotient.eq_iff_equiv.2 (Lpo.trunc_equiv h))

end Pom

private inductive TreeNode {l : Type} [Bot l] [LE l] (a b : Lpo l)
  | mk : (n : ℕ)
       → (a' : Lpo l)
       → (a' ≈ (a.trunc n).val ∧ a' ≤ b)
       → TreeNode a b

namespace TreeNode

def getLpo {l : Type} [Bot l] [LE l] {a b : Lpo l} (t : TreeNode a b) : Lpo l :=
  match t with | TreeNode.mk _ a _ => a

end TreeNode

lemma trunc_nodes_mono {l : Type} [Bot l] {a : Lpo l} {n m : ℕ}
  (hle : n ≤ m) : (a.trunc n).nodes ⊆ (a.trunc m).nodes := by {
  simp [Lpo.trunc ,Lpofin.nodes ,Lpo.nodes]
  intro x hx hlev; exact ⟨hx, le_trans hlev hle⟩
}

instance {l : Type} [Bot l] [LE l] {a b : Lpo l} : LE (TreeNode a b) where
  le | TreeNode.mk n a₁ _, TreeNode.mk m a₂ _ => n ≤ m ∧ a₁ ≤ a₂

instance {l : Type} [Bot l] [Preorder l] {a b: Lpo l} : Preorder (TreeNode a b) where
  le_refl t := by cases t; unfold LE.le; unfold instLETreeNode; simp [le_refl]
  le_trans t u v := by {
    cases t with | mk n a₁ _ =>
    cases u with | mk m a₂ _ =>
    cases v with | mk o a₃ _ =>
      unfold LE.le at *; unfold instLETreeNode at *; simp at *
      intro hnm h12 hmo h23
      exact ⟨le_trans hnm hmo, le_trans h12 h23⟩
  }

instance {l : Type} [Bot l] [PartialOrder l] {a b : Lpo l} : PartialOrder (TreeNode a b) where
  le_antisymm t u := by {
    cases t with | mk n a₁ _ =>
    cases u with | mk m a₂ _ =>
      unfold LE.le; unfold Preorder.toLE; unfold instPreorderTreeNode
      simp; unfold instLETreeNode; simp
      intro hnm h12 hmn h21
      exact ⟨le_antisymm hnm hmn, le_antisymm h12 h21⟩
  }

instance {l : Type} [Preorder l] [OrderBot l] {a b : Lpo l} : IsStronglyAtomic (TreeNode a b) where
  exists_covBy_le_of_lt := by {
    intro t u hlt
    cases t with | mk n a₁ h₁ =>
    cases u with | mk m a₂ h₂ =>
      rcases hlt with ⟨⟨hnm, hle⟩, hl⟩
      use TreeNode.mk (n + 1) (a₂.trunc (n+1)) (by {
        constructor
        · sorry
        · exact le_trans (Lpo.trunc_le (a := a₂) (n := n+1)) h₂.2
      })
      refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
      · sorry
      · sorry
      · sorry
      · exact Lpo.trunc_le
  }

lemma tree_node_finite_branching {l : Type} [Bot l] [Preorder l] (a b : Lpo l)
  (t : TreeNode a b) : { u | t ⋖ u }.Finite := by {
    sorry
  }

lemma tree_has_infinite_path {l : Type} [Bot l] [Preorder l] {a b : Lpo l}
  (root : TreeNode a b) : (Set.Ici root).Infinite := by {
    sorry
  }

theorem pom_ge_iff_ge_fin {l : Type}
  [CompletePartialOrder l] [OrderBot l] {p q : Pom l}
  (hle : ∀ n, p.trunc n ≤ q) : p ≤ q := by {
  rcases Quotient.exists_rep p with ⟨a, ha⟩
  rcases Quotient.exists_rep q with ⟨b, hb⟩
  subst ha; subst hb
  unfold Pom.trunc at hle; simp at hle
  rcases a.property.rel.single_rooted with ⟨x, hx⟩
  rcases b.property.rel.single_rooted with ⟨y, hy⟩
  let b₀ := Lpo.singleton y (b.lab y)
  let root : TreeNode a b := TreeNode.mk 0 b₀ (by sorry)
  rcases exists_seq_covby_of_forall_covby_finite
          (tree_node_finite_branching a b)
          (tree_has_infinite_path root) with ⟨f, h₀, hsucc⟩
  let a' := sSup { ai | ∃ i : ℕ, TreeNode.getLpo (f i) = ai }
  have heq : a ≈ a' := by sorry -- Need a lemma for this
  refine ⟨a', b, ?_, Quotient.sound heq, rfl⟩
  unfold a'; refine (isLUB_le_iff (lpo_sup_is_lub ?_ ?_)).2 ?_
  · simp [DirectedOn]; intro i j; use (max i j)
    sorry
  · use TreeNode.getLpo (f 0); simp
  · unfold upperBounds; simp; intro i
    rcases hi : f i with ⟨j, c, hc⟩; simp [TreeNode.getLpo]
    exact hc.2
}
