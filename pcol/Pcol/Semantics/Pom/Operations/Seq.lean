import Pcol.Semantics.Lpo.Operations.Seq
import Pcol.Semantics.Pom.FinApprox

namespace Pomfin

lemma exists_copy_fn {l : Type} [PartialOrder l] [OrderBot l] (α β : Lpofin l) :
    Nonempty (Lpofin.CopyFn α β) := by
  have hc : Cardinal.mk (α.branches × β.nodes) ≤ Cardinal.mk α.nodes.compl := by
    refine le_of_le_of_eq Cardinal.mk_le_aleph0 ?_
    symm; exact @Cardinal.mk_eq_aleph0 _ _ α.property.infinite_compl.to_subtype
  have ⟨s, hsub, hc'⟩ := Cardinal.le_mk_iff_exists_subset.mp hc
  have ⟨e_base⟩ := Cardinal.eq.mp hc'.symm
  let e φ : β.nodes ≃ Set.range (fun x ↦ (e_base (φ, x)).val) := {
    toFun x := ⟨e_base (φ, x), Set.mem_range.mpr ⟨_, rfl⟩⟩
    invFun y := (e_base.symm ⟨y, by {
      have ⟨x, hx⟩ := Set.mem_range.mp y.property; rw [← hx]; exact Subtype.coe_prop _
   }⟩).snd
    left_inv x := by simp only [Subtype.coe_eta, Equiv.symm_apply_apply]
    right_inv y := by
      ext; simp only
      have ⟨x, hx⟩ := Set.mem_range.mp y.property
      have {h} : ⟨y.val, h⟩ = e_base (φ, x) := by
        ext; exact hx.symm
      rw [this]; simp only [Equiv.symm_apply_apply]; exact hx
  }
  refine ⟨⟨fun φ ↦ β.permute (e φ), fun φ ↦ ⟨?_, ?_, ?_⟩⟩⟩
  · symm; exact ⟨e φ, rfl⟩
  · refine Set.disjoint_left.mpr ?_; intro x hx hx'
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hx'
    refine (Set.mem_compl_iff _ _).mp (hsub ?_) hx; exact Subtype.coe_prop _
  · intro ψ hne; refine Set.disjoint_left.mpr ?_; intro x hx hx'
    obtain ⟨y, rfl⟩ := Set.mem_range.mp hx
    have ⟨z, heq⟩ := Set.mem_range.mp hx'
    have := e_base.injective (Subtype.val_injective heq)
    exact hne (Prod.mk_inj.mp this).1.symm

noncomputable def seq {l : Type} [DCPO l] [OrderBot l] (p q : Pomfin l) : Pomfin l :=
  Quotient.map₂
    (fun α β ↦ Lpofin.seq α β (Classical.choice (exists_copy_fn α β)))
    (fun _ _ h _ _ h' ↦ Lpofin.seq_isomorphic h h')
    p q

lemma seq_monotone {l : Type} [DCPO l] [OrderBot l] {p p' q q' : Pomfin l}
    (hle : p ≤ p') (hle' : q ≤ q') : seq p q ≤ seq p' q' := by
  obtain ⟨α, rfl, α', rfl, hle₁⟩ := Pomfin.le_iff.mp hle
  obtain ⟨β, rfl, β', rfl, hle₂⟩ := Pomfin.le_iff.mp hle'
  have ⟨g⟩ := exists_copy_fn α' β'
  let up (φ : α.branches) : α'.branches :=
    ⟨φ.val, Lpofin.branches_monotone hle₁ φ.property⟩
  have h (φ : α.branches) :
      ∃ γ : Lpofin l, γ ≈ β ∧ γ ≤ g (up φ) := by
    have ⟨e, heq⟩ := (g.property (up φ)).1
    let e' := Lpo.perm_subset e.symm hle₂.nodes
    refine ⟨β.permute e', ?_, ?_⟩
    · symm; exact ⟨e', rfl⟩
    · refine Lpofin.le_iff.mpr ?_
      refine le_of_le_of_eq (Lpo.permute_monotone hle₂ (Lpo.perm_subset_ext)) ?_
      symm; exact Lpo.permute_symm heq
  choose f hf using h
  refine ⟨Lpofin.seq α β ⟨f, ?_⟩, ?_, Lpofin.seq α' β' g, ?_, ?_⟩
  · intro φ; refine ⟨(hf φ).1, ?_, ?_⟩
    · refine Set.disjoint_of_subset ?_ ?_ (g.property (up φ)).2.1
      · exact hle₁.nodes
      · exact (hf φ).2.nodes
    · intro ψ hne
      refine Set.disjoint_of_subset ?_ ?_ ((g.property (up φ)).2.2 (up ψ) ?_)
      · exact (hf φ).2.nodes
      · exact (hf ψ).2.nodes
      · unfold up; simpa only [ne_eq, Subtype.mk.injEq, SetLike.coe_eq_coe]
  · refine (congrArg _ (Quotient.map₂_mk _ _ _ _)).trans ?_
    refine val_mem_to_pom.mp (Quotient.eq_iff_equiv.mpr ?_)
    exact Lpofin.seq_isomorphic (Setoid.refl _) (Setoid.refl _)
  · refine (congrArg _ (Quotient.map₂_mk _ _ _ _)).trans ?_
    refine val_mem_to_pom.mp (Quotient.eq_iff_equiv.mpr ?_)
    exact Lpofin.seq_isomorphic (Setoid.refl _) (Setoid.refl _)
  · refine Lpofin.seq_monotone hle₁ hle₂ ?_
    intro φ; exact (hf φ).2

end Pomfin

namespace Pom

noncomputable def seq {l : Type} [DCPO l] [OrderBot l] [ScottCompact l] :
    Pom l → Pom l → Pom l :=
  Pom.ext₂ (fun p q ↦ (Pomfin.seq p q).to_pom) Pomfin.seq_monotone

lemma seq_monotone {l : Type} [DCPO l] [OrderBot l] [ScottCompact l] {p p' q q' : Pom l} :
    p ≤ p' → q ≤ q' → seq p q ≤ seq p' q' := ext₂_monotone

open OmegaCompletePartialOrder

lemma seq_continuous {l : Type} [DCPO l] [OrderBot l] [ScottCompact l]
    {c c' : Chain (Pom l)} :
    seq (ωSup c) (ωSup c') = ωSup {
      toFun n := seq (c n) (c' n)
      monotone' _ _ hle := seq_monotone (c.monotone' hle) (c'.monotone' hle)
    } := ext₂_continuous

end Pom
