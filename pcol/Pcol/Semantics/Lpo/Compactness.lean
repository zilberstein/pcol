import Pcol.Semantics.Lpo.FinApprox

lemma way_below_finnaprox {l : Type}
    [DCPO l] [OrderBot l]
    {α β : Lpo l} (h : ∀ x, ScottCompact (β.lab x)) :
    α ≪ β ↔ α ∈ β.finapprox := by
  constructor
  · intro h
    obtain ⟨γ, ⟨hγ, hfin⟩, hα⟩ :=
      h β.finapprox (le_of_eq Lpo.sup_finapprox_eq_self)
    refine ⟨hα.trans hγ, hfin.subset ?_⟩
    exact hα.nodes
  · intro ⟨hαβ, hfin⟩ d hβsup
    have h : ∀ x : ↑α.nodes, ∃ γ ∈ d, x.val ∈ γ.nodes ∧ α.lab x ≤ γ.lab x := by
      intro ⟨x, hx⟩
      obtain ⟨β', hβ'⟩ := d.nonempty
      -- Since the labels are compact, get a γ₁ ∈ d such that α.lab x ≤ γ₁.lab x
      obtain ⟨_, ⟨γ₁, hγ₁, rfl⟩, hlab⟩ :=
        h x (d.image _ (lab_monotone x)) (hβsup.lab x)
      -- Get a γ₂ ∈ d such that x ∈ γ₂.nodes
      have hx' := hβsup.nodes (hαβ.nodes hx)
      simp only [DSet.dSup, DCPO.dSup, Lpo.nodes, lpo_base_sup, Set.mem_iUnion, exists_prop] at hx'
      obtain ⟨γ₂, hγ₂, hx'⟩ := hx'
      -- Since d is directed, get an upper bound γ₁,γ₂ ≤ γ
      obtain ⟨γ, hγ, hle₁, hle₂⟩ := d.directed _ hγ₁ _ hγ₂
      refine ⟨γ, hγ, ?_, ?_⟩
      · exact hle₂.nodes hx'
      · exact (hαβ.lab x).trans (hlab.trans (hle₁.lab x))
    choose f hf using h
    let s := Set.range f
    have hs (x : ↑α.nodes) : f x ∈ s := Set.mem_range.mpr ⟨x, rfl⟩
    have hsub : s ⊆ d := by
      intro _ h; obtain ⟨x, rfl⟩ := Set.mem_range.mp h; exact (hf x).1
    have hfin : s.Finite := @Set.finite_range _ _ _ hfin
    obtain ⟨γ, hγ, hub⟩ := d.finite_upper_bound hsub hfin
    -- α and γ have sSup d as a common upper bound
    have hαle := hαβ.trans hβsup
    have hγle := DSet.le_dSup hγ
    have hnode : α.nodes ⊆ γ.nodes := by
      intro x hx; refine (hub _ (hs ⟨x, hx⟩)).nodes ?_
      exact (hf ⟨x, hx⟩).2.1
    refine ⟨γ, hγ, lpo_le_of_common_upper_bound hαle hγle hnode ?_⟩
    · intro x; by_cases hx : x ∈ α.nodes
      · exact (hf ⟨x, hx⟩).2.2.trans ((hub _ (hs ⟨x, hx⟩)).lab x)
      · exact le_of_eq_of_le (α.property.lab_dom _ hx) bot_le

lemma lpo_fin_compact {l : Type} [DCPO l] [OrderBot l] (α : Lpofin l)
    (h : ∀ x, ScottCompact (α.lab x)) : ScottCompact α.val :=
  (way_below_finnaprox h).mpr ⟨le_refl _, α.property⟩

def ext {l X : Type} [PartialOrder l] [OrderBot l] [DCPO X]
    (f : Lpofin l → X) (hf : Monotone f) (α : Lpo l) : X :=
  (α.finapprox'.image _ hf).dSup

-- This is pretty strong, but I'm not sure of a better way to express the property
def CompactType (X : Type) [DCPO X] : Prop :=
  ∀ x : X, ScottCompact x

lemma iSup_combine {X Y Z : Type}
    [LE X] [SupSet X] [Preorder Y] [CompletePartialOrder Z]
    {d : Set X} {f : X → Set Y} {g : Y → Z}
    (hd : DirectedOn LE.le d) (hf : ∀ x ∈ d, DirectedOn LE.le (f x)) (hg : Monotone g) :
    (⨆ x ∈ d, ⨆ y ∈ f x, g y) = ⨆ y ∈ { y | ∃ x ∈ d, y ∈ f x }, g y := by
  unfold iSup; sorry

lemma ext_monotone {l X : Type} [PartialOrder l] [OrderBot l] [DCPO X]
    {f : Lpofin l → X} (hf : Monotone f) : Monotone (ext f hf) := sorry

theorem ext_continuous {l X : Type} [DCPO X] [DCPO l] [OrderBot l]
    {f : Lpofin l → X} (hf : Monotone f) (hc : CompactType l) :
    DSet.ScottContinuous (ext_monotone hf) := by
  intro d; unfold ext
  refine le_antisymm (DSet.dSup_le ?_) ?_
  · rintro _ ⟨α, hα, rfl⟩
    obtain ⟨β, hβ, hle⟩ :=
      (way_below_finnaprox fun x ↦ hc (Lpo.lab _ x)).mpr
       ((Lpo.finapprox_convert (α' := α)).mpr hα)
        d (le_refl _)
    refine le_trans ?_ (DSet.le_dSup ?_) (b := (β.finapprox'.image f hf).dSup)
    · obtain ⟨γ, hγ, hαγ⟩ :=
        (way_below_finnaprox fun x ↦ hc (Lpo.lab _ x)).mpr
          ⟨hle, α.property⟩
          β.finapprox
          (le_of_eq Lpo.sup_finapprox_eq_self)
      exact
        (hf hαγ).trans
          (DSet.le_dSup (DSet.image_mem hγ.1)) (b := f ⟨γ, hγ.2⟩)
    · exact DSet.image_mem hβ
  · refine DSet.dSup_le ?_; rintro _ ⟨α, hα, rfl⟩
    refine DSet.dSup_le ?_; rintro _ ⟨β, hβ, rfl⟩
    refine DSet.le_dSup ?_; refine ⟨β, ?_, rfl⟩
    simp [Lpo.finapprox'] at *; refine le_trans hβ ?_
    exact DSet.le_dSup hα
