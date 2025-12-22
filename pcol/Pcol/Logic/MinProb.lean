import Pcol.ConvexPowerset
import Pcol.ConvexPowerset.Monad
import Pcol.Semantics.Lpo.Linearization

open Classical

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

lemma iInf_mul_minProb {X ι : Type} {t : C X} {A : Set X}
    {f : ι → ENNReal} (h : Nonempty ι) :
    iInf f * minProb t A = iInf fun x ↦ f x * minProb t A := by
  refine @ENNReal.iInf_mul _ _ _ h ?_
  intro c; exfalso; exact minProb_ne_top c

lemma iInf_C_mul_minProb {X Y : Type} {s : C X} {t : C Y} {A : Set Y}
    {f : Distr X → ENNReal} :
    (⨅ x ∈ s, f x) * minProb t A = ⨅ x ∈ s, f x * minProb t A := by
  rw [iInf_subtype', iInf_subtype']
  refine iInf_mul_minProb (nonempty_subtype.mpr ?_)
  exact s.property.nonempty

lemma iInf_next_mul {l X : Type} [Bot l] {α : Lpofin l} {s : Finset Node} {t : C X} {A : Set X}
    {f : ↑(Lpo.next α s) → ENNReal} (h : s ≠ ∅) :
    iInf f * minProb t A = iInf fun x ↦ f x * minProb t A := by
  refine iInf_mul_minProb ?_
  clear f; induction s using Finset.induction with
  | empty => contradiction
  | @insert x s hx ih =>
    by_cases hemp : s.Nonempty
    · obtain ⟨y, hys, hy, hs⟩ := ih hemp.ne_empty
      by_cases hxy : α.rel x y
      · refine ⟨x, Finset.mem_insert_self _ _, ?_, ?_⟩
        · exact (α.val.property.rel_dom hxy).1
        · intro z hz; refine Finset.mem_insert.mp.mt (not_or.mpr ⟨?_, ?_⟩)
          · rintro rfl; exact α.val.property.rel.irrefl _ hz
          · exact hs z (α.val.property.rel.trans hz hxy)
      · refine ⟨y, ?_, hy, ?_⟩
        · exact Finset.mem_insert_of_mem hys
        · intro z hz; refine Finset.mem_insert.mp.mt (not_or.mpr ⟨?_, ?_⟩)
          · rintro rfl; exact hxy hz
          · exact hs _ hz
    · refine ⟨x, Finset.mem_insert_self _ _, ?_, ?_⟩
      · sorry -- Will need to add assumptions so that s ⊆ α.nodes
      · intro y hy hins; rcases Finset.mem_insert.mp hins with rfl | hy
        · exact α.val.property.rel.irrefl _ hy
        · rw [Finset.not_nonempty_iff_eq_empty.mp hemp] at hy
          exact Finset.not_mem_empty _ hy

lemma mul_iInf_next {l X : Type} [Bot l] {α : Lpofin l} {s : Finset Node} {t : C X} {A : Set X}
    {f : ↑(Lpo.next α s) → ENNReal} (h : s ≠ ∅) :
    minProb t A * iInf f = iInf fun x ↦ minProb t A * f x :=
  (mul_comm _ _).trans ((iInf_next_mul h).trans
    (iInf_congr fun _ ↦ mul_comm _ _))

lemma minProb_mono {X : Type} {s t : C X} {A : Set X} (h : s ≤ t) :
    minProb s A ≤ minProb t A :=
  iInf_le_iInf_of_subset (le_iff_supset.mp h)
