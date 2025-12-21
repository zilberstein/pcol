import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.FinApprox
import Pcol.Semantics.Lpo.Order

namespace Lpo

variable {l : Type} [PartialOrder l] [OrderBot l]
variable (fork : l)

open Classical

noncomputable def par_base (x : Node) (α β : Lpofin l) : Lpo_base l := {
  nodes := Set.insert x (α.nodes ∪ β.nodes)
  rel y z := (y = x) ∨ α.rel y z ∨ β.rel y z
  lab y := if x = y then fork else if y ∈ α.nodes then α.lab y else β.lab y
  form y := fun v ↦ (x = y) ∨ (y ∈ α.nodes ∧ α.form y v) ∨ (y ∈ β.nodes ∧ β.form y v)
}

lemma par_valid (x : Node) (α β : Lpofin l)
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes) :
    is_valid_lpo (par_base fork x α β) := sorry

lemma par_finite (x : Node) (α β : Lpofin l) : (par_base fork x α β).nodes.Finite :=
  Set.Finite.insert _ (Set.Finite.union α.property β.property)

noncomputable def par_fin (x : Node) (α β : Lpofin l)
    (hx : x ∉ α.nodes) (hx' : x ∉ β.nodes) (hd : Disjoint α.nodes β.nodes) :
    Lpofin l :=
  ⟨⟨par_base fork x α β, par_valid fork x α β hx hx' hd⟩, par_finite fork x α β⟩
