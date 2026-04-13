import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Order

namespace Lpofin
open Classical

variable {l : Type} [PartialOrder l] [OrderBot l]

-- stuck is a path condition formula indicating that the execution will definitely
-- encounter a ⊥ node
def stuck (α : Lpofin l) : Form Node := Form.sOr fun x : ↑α.val.bots ↦ α.form x.val

lemma stuck_antitone : @Antitone (Lpofin l) _ _ _ stuck := by
  intro α β hle v ⟨⟨x, hx, hlab⟩, hform⟩
  rcases hle.succ _ hx with hx' | ⟨y, ⟨hy, hlab'⟩, hyx⟩
  · refine ⟨⟨x, hx', ?_⟩, ?_⟩
    · refine le_antisymm ?_ bot_le
      rw [← hlab]; exact hle.lab x
    · refine (congrFun (hle.form x hx') v).mpr ?_
      exact hform
  · refine ⟨⟨y, hy, hlab'⟩, ?_⟩
    refine (congrFun (hle.form _ hy) _).mpr ?_
    refine (β.val.property.form _ (hle.nodes hy)).2 _ hyx _ ?_
    exact hform

-- A node is in the exntensible set if it is possible for it not be stuck
noncomputable def extens (α : Lpofin l) : Finset Node :=
  α.nodes_finset.filter fun x ↦ ¬ α.form x ≤ α.stuck

lemma extens_not_bot {α : Lpofin l} {x : Node} : x ∈ α.extens → α.lab x ≠ ⊥ := by
  intro h; simp [extens] at h; intro heq; apply h.2; intro v hform
  refine ⟨⟨x, ?_, heq⟩, hform⟩
  exact (α.val.property.form_dom x).mp ⟨v, hform⟩

lemma extens_subset_nodes {α : Lpofin l} : ∀ x ∈ α.extens, x ∈ α.nodes := by
  intro x hx; exact (Set.Finite.mem_toFinset _).mp (Finset.mem_filter.mp hx).1

lemma extens_monotone : @Monotone (Lpofin l) _ _ _ extens := by
  intro α β hle x; simp [extens]; intro hx hstuck
  have hx' := (Set.Finite.mem_toFinset _).mp hx
  refine ⟨(Set.Finite.mem_toFinset _).mpr (hle.nodes hx'), fun hc ↦ ?_⟩
  refine hstuck (fun v hform ↦ stuck_antitone hle v (hc v ?_))
  simp [Lpofin.form]; rw [← hle.form x hx']; exact hform

lemma le_extens {α β : Lpofin l} (hle : α ≤ β) :
    α.extens = β.extens.filter fun x ↦ ¬ (β.form x ≤ α.stuck) := by
  ext x; constructor
  · intro hx; refine Finset.mem_filter.mpr ⟨extens_monotone hle hx, ?_⟩
    intro c; refine (Finset.mem_filter.mp hx).2 (le_trans ?_ c)
    exact le_form hle
  · intro hx; obtain ⟨hx, hstk⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx', _⟩ := Finset.mem_filter.mp hx
    apply (Set.Finite.mem_toFinset _).mp at hx'
    rcases hle.succ _  hx' with hxα | ⟨y, ⟨hy, hbot⟩, hyx⟩
    · refine Finset.mem_filter.mpr ⟨(Set.Finite.mem_toFinset _).mpr hxα, ?_⟩
      intro c; refine hstk (le_of_eq_of_le (Eq.symm ?_) c)
      exact hle.form _ hxα
    · exfalso; refine hstk (((β.val.property.form y (hle.nodes hy)).2 _ hyx).trans ?_)
      refine le_of_eq_of_le (Eq.symm (hle.form _ hy)) ?_
      intro v hform; exact ⟨⟨y, hy, hbot⟩, hform⟩

def conj (α : Lpofin l) (S : Finset Node) : Form Node :=
  Form.sAnd fun x : ↑S ↦ α.form x.val

def branches_set (α : Lpofin l) : Set (Form Node) :=
  α.conj ''
  { S : Finset Node
  | S.Nonempty ∧
    S ⊆ α.extens ∧
    (α.conj S).sat ∧
    α.conj S ≤ α.stuck.not ∧
    ∀ T, S ⊂ T → T ⊆ α.extens → ¬ Form.sat (fun v ↦ ∀ x ∈ T, α.form x v)
  }

lemma branches_finite (α : Lpofin l) : α.branches_set.Finite := by
  refine Set.Finite.image _ ?_
  refine Set.Finite.subset α.extens.powerset.finite_toSet ?_
  intro s ⟨_, hsub, _⟩; simp only [Finset.coe_powerset, Set.mem_preimage, Set.mem_powerset_iff,
    Finset.coe_subset, hsub]

noncomputable def branches (α : Lpofin l) : Finset (Form Node) := α.branches_finite.toFinset

lemma branches_set_monotone : @Monotone (Lpofin l) _ _ _ branches_set := by
  rintro α β hle φ ⟨S, ⟨hne, hsub, hsat, hstuck, hmax⟩, hφ⟩; subst hφ
  refine ⟨S, ⟨hne, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact le_trans hsub (extens_monotone hle)
  · rcases hsat with ⟨v, hv⟩; use v; intro x
    refine (congrFun (hle.form x ?_) _).mp (hv x)
    have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
    exact (Set.Finite.mem_toFinset _).mp hx'
  · intro v hform hstuck'; refine hstuck v ?_ ?_
    · intro x; refine (congr_fun (hle.form x ?_) v).mpr (hform x)
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'
    · exact stuck_antitone hle v hstuck'
  · intro T hST hT ⟨v, hc⟩; obtain ⟨x, hxT, hxS⟩ := Finset.exists_of_ssubset hST
    have hform : α.conj S v := by
      intro y; refine (congrFun (hle.form _ ?_) _).mpr (hc _ ?_)
      · exact extens_subset_nodes _ (hsub y.property)
      · exact (Finset.ssubset_def.mp hST).1 y.property
    rcases hle.succ _ (extens_subset_nodes _ (hT hxT))
      with hx | ⟨y, hy, hyx⟩
    · refine hmax (insert x S) (Finset.ssubset_insert hxS) ?_ ?_
      · refine Finset.insert_subset (Finset.mem_filter.mpr ⟨?_, ?_⟩) hsub
        · exact (Set.Finite.mem_toFinset _).mpr hx
        · intro c; refine hstuck v hform ?_
          exact c v ((congrFun (hle.form _ hx) _).mpr (hc _ hxT))
      · use v; intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy'
        · exact (congrFun (hle.form y hx) _).mpr (hc y hxT)
        · refine (congrFun (hle.form y ?_) _).mpr (hc y ?_)
          · exact extens_subset_nodes _ (hsub hy')
          · exact Finset.mem_of_subset (Finset.ssubset_def.mp hST).1 hy'
    · refine hstuck v hform ⟨⟨y, hy⟩, ?_⟩
      refine (congrFun (hle.form _ hy.1) _).mpr ?_
      exact (β.val.property.form _ (hle.nodes hy.1)).2 _ hyx v (hc _ hxT)
  · ext1 v; refine forall_congr fun x ↦ ?_; ext; constructor
    · intro h; refine (congr_fun (hle.form x ?_) v).mpr h
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'
    · intro h; refine (congr_fun (hle.form x ?_) v).mp h
      have hx' := Finset.mem_of_mem_filter _ (hsub x.property)
      exact (Set.Finite.mem_toFinset _).mp hx'

lemma le_branches_set {α β : Lpofin l} (hle : α ≤ β) :
    α.branches_set = { φ ∈ β.branches_set | φ ≤ α.stuck.not } := by
  ext φ; constructor
  · intro h; constructor
    · exact branches_set_monotone hle h
    · rcases h with ⟨_, ⟨_, _, _, hstuck, _⟩, rfl⟩
      exact hstuck
  · rintro ⟨⟨S, ⟨hne, hsub, ⟨v, hsat⟩, _, hmax⟩, rfl⟩, hstuck⟩
    have hS x (hx : x ∈ S) : x ∈ α.nodes := by
      have hx' := extens_subset_nodes _ (hsub hx)
      rcases hle.succ _ hx' with hxα | ⟨y, hbot, hyx⟩
      · exact hxα
      · exfalso; refine forall_not_of_not_exists (hstuck v hsat) ⟨y, hbot⟩ ?_
        refine (congrFun (hle.form y hbot.1) _).mpr ?_
        refine (β.val.property.form y (hle.nodes hbot.1)).2 _ hyx v ?_
        exact hsat ⟨_, hx⟩
    refine ⟨S, ⟨hne, ?_, ⟨v, ?_⟩, ?_, ?_⟩, ?_⟩
    · intro x hx; rw [le_extens hle]; refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · exact hsub hx
      · intro c; exact hstuck v hsat (c v (hsat ⟨x, hx⟩))
    · intro x; exact (congrFun (hle.form x (hS _ x.property)) _).mpr (hsat x)
    · refine le_trans ?_ hstuck; intro u hu x
      exact (congrFun (hle.form _ (hS _ x.property)) _).mp (hu x)
    · intro T hST hT ⟨u, hu⟩; refine hmax T hST ?_ ?_
      · exact le_trans hT (extens_monotone hle)
      · use u; intro x hx; refine (congrFun (hle.form _ ?_) _).mp (hu _ hx)
        exact extens_subset_nodes _ (hT hx)
    · ext1 u; refine forall_congr fun x ↦ ?_
      exact congrFun (hle.form x (hS _ x.property)) _

lemma branches_monotone : @Monotone (Lpofin l) _ _ _ branches := by
  unfold branches; intro α β hle; simp; exact branches_set_monotone hle

lemma branches_not_mutually_sat {α : Lpofin l} {φ ψ : Form Node}
    (hφ : φ ∈ α.branches) (hψ : ψ ∈ α.branches) (hneq : φ ≠ ψ) :
    ∀ v, ¬ (φ v ∧ ψ v) := by
  intro v ⟨h₁, h₂⟩
  rcases (Set.Finite.mem_toFinset _).mp hφ with ⟨S, ⟨_, hsub, _, _, hmax⟩, rfl⟩
  rcases (Set.Finite.mem_toFinset _).mp hψ with ⟨T, ⟨_, hsub', _, _, hmax'⟩, rfl⟩
  refine hmax (S ∪ T) ⟨Finset.subset_union_left, ?_⟩ ?_ ?_
  · intro h; apply hneq; refine congrArg _ ?_; ext x; constructor
    · intro hx; by_contra ht; refine hmax' (insert x T) ?_ ?_ ?_
      · exact Finset.ssubset_insert ht
      · intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
        · exact hsub hx
        · exact hsub' hy
      · use v; intro y hy; rcases Finset.mem_insert.mp hy with rfl | hy
        · exact h₁ ⟨y, hx⟩
        · exact h₂ ⟨y, hy⟩
    · intro hx; exact h (Finset.subset_union_right hx)
  · intro x hx; rcases Finset.mem_union.mp hx with hx | hx
    · exact hsub hx
    · exact hsub' hx
  · use v; intro x hx; rcases Finset.mem_union.mp hx with hx | hx
    · exact h₁ ⟨x, hx⟩
    · exact h₂ ⟨x, hx⟩

def CopyFn (α β : Lpofin l) : Type :=
  { f : ↑α.branches → Lpofin l //
    ∀ φ : ↑α.branches,
      f φ ≈ β ∧
      Disjoint α.nodes (f φ).nodes ∧
      ∀ ψ, φ ≠ ψ → Disjoint (f φ).nodes (f ψ).nodes
  }
instance {α β : Lpofin l} : FunLike (CopyFn α β) ↑α.branches (Lpofin l) where
  coe := Subtype.val
  coe_injective' _ _ h := Subtype.ext h

def CopyFn_extends {α α' β β' : Lpofin l}
    (hle : α ≤ α') (f : CopyFn α β) (g : CopyFn α' β') :=
  ∀ φ : ↑α.branches, f φ ≤ g ⟨φ.val, branches_monotone hle φ.property⟩

noncomputable def seq_base [DCPO l] (α β : Lpofin l) (f : CopyFn α β) : Lpo_base l := {
  nodes := α.nodes ∪ ⋃ φ : ↑α.branches, (f φ).nodes
  rel x y :=
    α.rel x y ∨
    ∃ φ : ↑α.branches,
      (f φ).rel x y ∨
      (φ ≤ α.form x ∧ y ∈ (f φ).nodes)
  lab x :=
    if hx : ∃ φ : ↑α.branches, x ∈ (f φ).nodes then
      (f hx.choose).lab x
    else
      α.lab x
  form x := if x ∈ α.nodes then α.form x else Form.sOr fun φ : ↑α.branches ↦ ((f φ).form x).and φ.val
}

lemma branch_implies_node {α : Lpofin l} {x : Node} :
    ∀ φ : ↑α.branches, φ ≤ α.form x → x ∈ α.val.nodes := by
  intro φ hle
  rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨hne, hsub, hsat, hstk, hmax⟩, heq⟩
  refine (α.val.property.form_dom x).mp ?_
  rcases hsat with ⟨v, hv⟩; use v; exact hle v ((congrFun heq _).mp hv)

lemma seq_nodes_finite [DCPO l] {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).nodes.Finite := by
  refine Set.finite_union.mpr ⟨α.property, ?_⟩
  refine Set.finite_iUnion ?_; intro φ; exact (f φ).property

lemma seq_rel_valid [DCPO l] {α β : Lpofin l} {f : CopyFn α β} :
    (seq_base α β f).rel.IsCausalityRel (seq_base α β f).nodes := by
  have h₁ := α.val.property
  have h₂ φ := (f φ).val.property
  rcases f with ⟨f, hf⟩
  have hd₁ φ := (hf φ).2.1
  have hd₂ φ ψ := (hf φ).2.2 ψ
  have contra {P : Prop} {s t : Set Node} {x : Node} (hd : Disjoint s t)
      (hs : x ∈ s) (ht : x ∈ t) : P :=
    False.elim (Set.disjoint_left.mp hd hs ht)
  constructor
  -- Transitivity
  · rintro x y z (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyz | ⟨ψ, hyz | ⟨hy', hz⟩⟩)
    · left; exact h₁.rel.trans hxy hyz
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2
        ((f ψ).val.property.rel_dom hyz).1
    · right; use ψ; right; refine ⟨?_, hz⟩
      refine hy'.trans ?_; exact (h₁.form x (h₁.rel_dom hxy).1).2 y hxy
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 ((f φ).val.property.rel_dom hxy).2
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; left; exact (f φ).val.property.rel.trans hxy hyz
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyz).1
    · have hy := branch_implies_node ψ hy'
      exact contra (hd₁ φ) hy ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyz).1 hy
    · by_cases heq : φ = ψ
      · subst heq; right; use φ; right; refine ⟨hx, ?_⟩
        exact ((f φ).val.property.rel_dom hyz).2
      · exact contra (hd₂ φ ψ heq) hy ((f ψ).val.property.rel_dom hyz).1
    · have hy'' := branch_implies_node ψ hy'
      exact contra (hd₁ φ) hy'' hy
  -- Antisymmetry
  · rintro x y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩) (hyx | ⟨ψ, hyx | ⟨hy', hx'⟩⟩)
    · exact h₁.rel.antisymm hxy hyx
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).2 ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ ψ) (h₁.rel_dom hxy).1 hx'
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).2 ((f φ).val.property.rel_dom hxy).1
    · by_cases heq : φ = ψ
      · subst heq; exact (f φ).val.property.rel.antisymm hxy hyx
      · exact contra (hd₂ φ ψ heq)
          ((f φ).val.property.rel_dom hxy).2
          ((f ψ).val.property.rel_dom hyx).1
    · exact contra (hd₁ φ)
        (branch_implies_node ψ hy')
        ((f φ).val.property.rel_dom hxy).2
    · exact contra (hd₁ φ) (h₁.rel_dom hyx).1 hy
    · exact contra (hd₁ ψ) (branch_implies_node φ hx)
        ((f ψ).val.property.rel_dom hyx).2
    · exact contra (hd₁ ψ) (branch_implies_node φ hx) hx'
  -- Irreflexivity
  · rintro x (hxx | ⟨φ, hxx | ⟨hx, hx'⟩⟩)
    · exact h₁.rel.irrefl x hxx
    · exact (f φ).val.property.rel.irrefl x hxx
    · exact contra (hd₁ φ) (branch_implies_node φ hx) hx'
  -- Finitely Preceded
  · intro x; refine (seq_nodes_finite (α := α) (β := β) (f := ⟨f, hf⟩)).subset ?_
    rintro y (hyx | ⟨φ, hyx | ⟨hy, hx⟩⟩)
    · left; exact (h₁.rel_dom hyx).1
    · right; simp only [nodes, ne_eq, Set.mem_iUnion]
      use φ; exact ((h₂ φ).rel_dom hyx).1
    · left; exact branch_implies_node φ hy
  -- Finite Levels
  · intro n; refine (seq_nodes_finite (α := α) (β := β) (f := ⟨f, hf⟩)).subset ?_
    intro x ⟨hx, _⟩; exact hx
  -- Single-Rooted
  · obtain ⟨x, hx, hroot⟩ := h₁.rel.single_rooted; refine ⟨x, Or.inl hx, ?_⟩
    rintro y (hy | hy) hneq
    · left; exact hroot _ hy hneq
    · apply Set.mem_iUnion.mp at hy; rcases hy with ⟨φ, hy⟩
      right; use φ; right; refine ⟨?_, hy⟩
      intro v hform
      have ⟨S, ⟨⟨y, hy⟩, hext, ⟨v', hsat⟩, _⟩, hconj⟩ := (Set.Finite.mem_toFinset _).mp φ.property
      rw [← hconj] at hform; have := hform ⟨_, hy⟩
      by_cases heq : x = y
      · subst heq; exact this
      · have hy := extens_subset_nodes _ (hext hy)
        exact (α.val.property.form _ hx).2 _ (hroot _ hy heq) _ this

lemma seq_valid [DCPO l] (α β : Lpofin l) (f : CopyFn α β) :
    is_valid_lpo (seq_base α β f) := by
  constructor
  -- Rel Domain
  · intro x y hrel; cases hrel with
    | inl hrel =>
        refine ⟨Or.inl ?_, Or.inl ?_⟩
        · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).1
        · simp [Lpofin.nodes, Lpofin.rel] at *; exact (α.val.property.rel_dom hrel).2
    | inr hrel =>
        rcases hrel with ⟨φ, (hrel | ⟨hx, hy⟩)⟩
        · constructor <;> refine Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).1
          · simp [Lpofin.nodes, Lpofin.rel] at *; exact ((f ⟨φ, _⟩).val.property.rel_dom hrel).2
        · refine ⟨Or.inl ?_, Or.inr (Set.mem_iUnion.mpr ⟨φ, ?_⟩)⟩
          · exact branch_implies_node φ hx
          · exact hy
  -- Label Domain
  · intro x hx; apply (Set.mem_union _ _ _).mpr.mt at hx
    simp only [Set.mem_iUnion, Subtype.exists, not_or, not_exists] at hx
    rcases hx with ⟨hx, hx'⟩
    simp only [seq_base, Subtype.exists]
    refine (dif_neg ?_).trans (α.val.property.lab_dom _ hx)
    intro ⟨φ, hφ, hx⟩; exact hx' _ hφ hx
  -- Rel Properties
  · exact seq_rel_valid
  -- Bot Successors
  · rintro x hlab y (hxy | ⟨φ, hxy | ⟨hx, hy⟩⟩)
    · have hx := (α.val.property.rel_dom hxy).1
      refine (α.val.property.bot x).mt ?_ ?_
      · intro hc; exact hc _ hxy
      · rw [← hlab]; refine Eq.trans ?_ (dif_neg ?_).symm
        · rfl
        · intro ⟨φ, hc⟩; exact Set.disjoint_left.mp (f.property φ).2.1 hx hc
    · have hx := ((f φ).val.property.rel_dom hxy).1
      refine ((f φ).val.property.bot x).mt ?_ ?_
      · intro hc; exact hc _ hxy
      · rw [← hlab]; refine ((dif_pos ⟨φ, hx⟩).trans ?_).symm
        refine congrArg₂ Lpo.lab (congrArg _ (congrArg _ ?_)) rfl
        refine (not_not.mp (((f.property φ).2.2 _).mt ?_)).symm
        refine Set.not_disjoint_iff.mpr ⟨x, hx, ?_⟩
        exact Exists.choose_spec (p := fun ψ ↦ x ∈ (f ψ).nodes) _
    · have hx' := branch_implies_node φ hx
      simp only [seq_base, nodes] at hlab
      rcases (Set.Finite.mem_toFinset _).mp φ.2 with ⟨S, ⟨_, _, ⟨v, hv⟩, hstk, _⟩, heq⟩
      rw [← heq] at hx; have hform := hx v hv
      have : ¬ (∃ φ, x ∈ (f φ).nodes) := by
        intro ⟨ψ, hx⟩; exact Set.disjoint_left.mp (f.property ψ).2.1 hx' hx
      have := (dif_neg this).symm.trans hlab
      exact hstk v hv ⟨⟨x, hx', this⟩, hform⟩
  -- Formula Domain
  · intro x; constructor
    · rintro ⟨v, hv⟩; by_cases hx : x ∈ α.nodes <;>
      simp only [seq_base, Subtype.exists, hx, ↓reduceIte] at hv
      · left; exact (α.val.property.form_dom x).mp ⟨v, hv⟩
      · rcases hv with ⟨φ, hφ, _⟩; right
        simp only [Set.mem_iUnion]
        use φ; exact ((f φ).val.property.form_dom x).mp ⟨v, hφ⟩
    · simp only [seq_base, nodes, Subtype.exists, Set.mem_union, Set.mem_iUnion]
      rintro (hx | ⟨φ, hφ, hx⟩)
      · simp only [hx, ↓reduceIte]
        exact (α.val.property.form_dom x).mpr hx
      · have hx' : x ∉ α.val.nodes :=
          Set.disjoint_right.mp (f.2 ⟨φ, hφ⟩).2.1 hx
        simp only [hx', ↓reduceIte]
        obtain ⟨v, hv⟩ := ((f ⟨φ, hφ⟩).val.property.form_dom x).mpr hx
        have ⟨s, ⟨_, hs, ⟨v', hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp hφ
        refine ⟨(v ∩ (f ⟨φ, hφ⟩).nodes) ∪ (v' ∩ α.nodes), ⟨φ, hφ⟩, ?_, ?_⟩
        · refine (((f ⟨φ, hφ⟩).val.property.form _ hx).1 _ _ ?_).mp hv
          refine Set.disjoint_left.mpr ?_; intro y hy hrel
          rcases Set.mem_symmDiff.mp hy with ⟨hy, hy'⟩ | ⟨⟨hy, _⟩ | ⟨hy, ha⟩, hy'⟩
          · simp only [Set.mem_union, Set.mem_inter_iff, not_or, not_and] at hy'
            refine hy'.1 hy ?_
            exact ((f _).val.property.rel_dom hrel).1
          · exact hy' hy
          · exact Set.disjoint_right.mp (f.property _).2.1 ((f _).val.property.rel_dom hrel).1 ha
        · subst heq; simp only; intro y
          have hy' := extens_subset_nodes _ (hs y.property)
          refine ((α.val.property.form _ hy').1 _ _ ?_).mp (hsat y)
          refine Set.disjoint_left.mpr ?_; intro z hz hrel
          rcases Set.mem_symmDiff.mp hz with ⟨hzv', hz⟩ | ⟨⟨hzv, hz⟩ | h, hzv'⟩
          · simp only [Set.mem_union, Set.mem_inter_iff, not_or, not_and] at hz
            exact hz.2 hzv' (α.val.property.rel_dom hrel).1
          · refine Set.disjoint_left.mp (f.property _).2.1 ?_ hz
            exact (α.val.property.rel_dom hrel).1
          · exact hzv' h.1
  -- Formula Properties
  · rintro x (hx | hx) <;> refine ⟨?_, fun y hrel ↦ ?_⟩
    · simp only [seq_base, if_pos hx]
      refine Form.DependsOn.monotone _ ?_ (α.val.property.form _ hx).1
      intro y hrel; left; exact hrel
    · rcases hrel with hrel | ⟨φ, hrel | ⟨hform, hy⟩⟩
      · have hy : y ∈ α.nodes := (α.val.property.rel_dom hrel).2
        simp only [seq_base, if_pos hx, if_pos hy]
        exact (α.val.property.form _ hx).2 _ hrel
      · exfalso; refine Set.disjoint_left.mp (f.property φ).2.1 hx ?_
        exact ((f φ).val.property.rel_dom hrel).1
      · have hy' : y ∉ α.nodes :=
          Set.disjoint_right.mp (f.property φ).2.1 hy
        simp only [seq_base, if_pos hx, if_neg hy']
        refine le_trans ?_ hform; intro v ⟨ψ, hsat, hψ⟩
        have hy'' := ((f ψ).val.property.form_dom _).mp ⟨_, hsat⟩
        have := not_not.mp (((f.property φ).2.2 ψ).mt (Set.not_disjoint_iff.mpr ⟨_, hy, hy''⟩))
        subst this; exact hψ
    · simp only [Set.mem_iUnion] at hx; have ⟨φ, hx⟩ := hx
      have hx' : x ∉ α.nodes :=
        Set.disjoint_right.mp (f.property φ).2.1 hx
      simp only [seq_base, if_neg hx']
      have :
          (Form.sOr fun φ ↦ ((f φ).form x).and φ.val) =
          ((f φ).form x).and φ.val := by
        ext v; constructor
        · intro ⟨ψ, hform⟩; by_cases heq : φ = ψ
          · subst heq; exact hform
          · exfalso; have := Set.disjoint_left.mp ((f.property φ).2.2 _ heq) hx
            exact this (((f ψ).val.property.form_dom _).mp ⟨_, hform.1⟩)
        · intro hform; exact ⟨φ, hform⟩
      rw [this]
      refine Form.DependsOn.monotone _
        (?_ : ({ y | (f φ).rel y x } ∪ { y | φ.val ≤ α.form y }) ⊆ _)
        ?_
      · rintro y (hrel | hform)
        · right; use φ; left; exact hrel
        · right; use φ; right; exact ⟨hform, hx⟩
      · refine Form.DependsOn.and ?_ ?_
        · exact ((f φ).val.property.form  _ hx).1
        · have ⟨s, ⟨_, hs, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
          rw [← heq]
          refine Form.DependsOn.monotone _
            (?_ : (⋃ z : ↑s, { y | α.form z ≤ α.form y }) ⊆ _)
            ?_
          · intro y; simp only [Set.mem_iUnion]; intro ⟨z, hform⟩ v h; exact hform v (h z)
          · refine Form.DependsOn.sAnd fun z ↦ ?_
            have hz := extens_subset_nodes _ (hs z.property)
            refine (α.val.property.form _ hz).1.monotone _ ?_
            intro y hrel; have hy := (α.val.property.rel_dom hrel).1
            exact (α.val.property.form _ hy).2 _ hrel
    · rcases hrel with (hrel | ⟨φ, hrel | ⟨hform, hy⟩⟩)
      · have ⟨hx, hy⟩ := α.val.property.rel_dom hrel
        refine le_of_eq_of_le (if_pos hy) ?_
        refine le_of_le_of_eq ?_ (if_pos hx).symm
        exact (α.val.property.form _ hx).2 _ hrel
      · have ⟨hx, hy⟩ := (f φ).val.property.rel_dom hrel
        have hx' := Set.disjoint_right.mp (f.property φ).2.1 hx
        have hy' := Set.disjoint_right.mp (f.property φ).2.1 hy
        refine le_of_eq_of_le (if_neg hy') ?_
        refine le_of_le_of_eq ?_ (if_neg hx').symm
        intro v ⟨ψ, hform, hφ⟩
        have hy'' := ((f ψ).val.property.form_dom _).mp ⟨_, hform⟩
        have := not_not.mp (((f.property φ).2.2 ψ).mt (Set.not_disjoint_iff.mpr ⟨_, hy, hy''⟩))
        subst this; refine ⟨φ, ?_, hφ⟩
        exact ((f φ).val.property.form _ hx).2 _ hrel _ hform
      · exfalso; simp only [Set.mem_iUnion] at hx
        have ⟨ψ, hx⟩ := hx; refine Set.disjoint_right.mp (f.property ψ).2.1 hx ?_
        have ⟨s, ⟨_, _, ⟨v, hsat⟩, _⟩, heq⟩ := (Set.Finite.mem_toFinset _).mp φ.property
        rw [← heq] at hform; exact (α.val.property.form_dom _).mp ⟨_, hform _ hsat⟩

noncomputable def seq [DCPO l] (α β : Lpofin l) (f : CopyFn α β) : Lpofin l := {
  val := {
    val := seq_base α β f
    property := seq_valid α β f
  }
  property := seq_nodes_finite
}

lemma seq_monotone [DCPO l] {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hle₁ : α ≤ α') (hle₂ : β ≤ β') (hext : CopyFn_extends hle₁ f g) :
    seq α β f ≤ seq α' β' g := by
  constructor
  · simp only [Lpo.nodes, seq, seq_base, nodes,
      Subtype.exists, Set.union_subset_iff, Set.iUnion_subset_iff, Subtype.forall]
    constructor
    · intro x hx; left; exact hle₁.nodes hx
    · intro φ hφ x hx; right
      have hφ' := branches_monotone hle₁ hφ
      simp only [Set.mem_iUnion, Subtype.exists]
      exact ⟨φ, hφ', (hext ⟨φ, hφ⟩).nodes hx⟩
  · rintro x (hx | hx) y hyx
    · rcases hyx with (hyx | ⟨ψ, hyx | ⟨hx', hy⟩⟩)
      · left; exact hle₁.downcl x hx y hyx
      · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle₁.nodes hx)
          ((g ψ).val.property.rel_dom hyx).2
      · exfalso; exact Set.disjoint_left.mp (g.property ψ).2.1 (hle₁.nodes hx) hy
    · rcases Set.mem_iUnion.mp hx with ⟨φ, hx⟩
      rcases hyx with (hyx | ⟨ψ, hyx⟩)
      · exfalso; have hx' := (hext φ).nodes hx
        exact Set.disjoint_left.mp (g.property _).2.1
          (α'.val.property.rel_dom hyx).2
          hx'
      · by_cases heq : ψ = ⟨φ.val, branches_monotone hle₁ φ.property⟩
        · subst heq; rcases hyx with hyx | ⟨hy, hx'⟩
          · right; refine Set.mem_iUnion.mpr ⟨φ, ?_⟩;
            exact (hext φ).downcl x hx y hyx
          · left; sorry
        · exfalso
          refine Set.disjoint_left.mp ((g.property ψ).2.2 _ heq)
              ?_
              ((hext φ).nodes hx)
          rcases hyx with hyx | ⟨_, hx'⟩
          · exact ((g ψ).val.property.rel_dom hyx).2
          · exact hx'
  · simp only [Lpo.nodes, seq, seq_base, Subtype.exists, Set.mem_union, Finset.mem_coe,
      Set.mem_iUnion, Lpo.rel, eq_iff_iff]
    intro x hx y hy; sorry
  · intro x; by_cases hx : x ∈ (α.seq β f).nodes
    · rcases hx with hx | hx
      · have hx' : x ∈ α'.nodes := hle₁.nodes hx
        simp only [Lpo.lab, seq, seq_base, hx, ↓reduceIte, hx']
        sorry -- exact hle₁.lab x
      · rcases Set.mem_iUnion.mp hx with ⟨φ, hx⟩
        have hnα := Set.disjoint_right.mp (f.property φ).2.1 hx
        have hx' := (hext φ).nodes hx
        have hnα' := Set.disjoint_right.mp (g.property _).2.1 hx'
        simp only [Lpo.lab, seq, seq_base, hnα, ↓reduceIte, hnα']
        sorry
    · exact le_of_eq_of_le ((α.seq β f).val.property.lab_dom _ hx) bot_le
  · rintro x (hx | hx)
    · have hx' := hle₁.nodes hx
      simp only [Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
      simp only [hx, hx', ↓reduceIte]; exact hle₁.form x hx
    · rcases Set.mem_iUnion.mp hx with ⟨φ, h⟩
      simp only [Lpo.form, Lpofin.nodes, Lpo.nodes, seq, seq_base] at *
      have hx₁ := Set.disjoint_right.mp (f.property φ).2.1 h
      have hx₂ := Set.disjoint_right.mp (g.property _).2.1 ((hext φ).nodes h)
      simp only [Lpofin.nodes, Lpo.nodes] at hx₁
      simp only [Lpofin.nodes, Lpo.nodes] at hx₂
      simp only [hx₁, ↓reduceIte, hx₂]
      ext v; constructor
      · intro ⟨ψ, hψ, hφ⟩
        have heq : φ = ψ := by
          by_contra hc
          have hd := (f.property φ).2.2 ψ hc
          have hx := Set.disjoint_left.mp hd h
          exact ((f ψ).val.property.form_dom x).mp.mt hx ⟨v, hψ⟩
        subst heq; exact ⟨_, (congrFun ((hext _).form _ h) _).mp hψ, hφ⟩
      · intro ⟨ψ, hψ⟩; sorry
  · sorry

lemma seq_isomorphic [DCPO l] {α α' β β' : Lpofin l} {f : CopyFn α β} {g : CopyFn α' β'}
    (hα : α ≈ α') (hβ : β ≈ β') : seq α β f ≈ seq α' β' g := by
  have ⟨e₁, he₁⟩ := hα; have ⟨e₂, he₂⟩ := hβ; sorry

end Lpofin
