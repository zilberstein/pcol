import Pcol.Semantics.Lpo.Linearization
import Pcol.Semantics.Pom.FinApprox

namespace Pom

open OmegaCompletePartialOrder

noncomputable def lin_fin (t : Type → Type) (α act test : Type)
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t]
    [∀ {β : Type}, Preorder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Linearizable t]
    (p : Pomfin (Label act test)) : α → t α :=
  p.lift Lpo.lin (fun _ _ ↦ Lpo.lin_iso)

lemma lin_fin_monotone (t : Type → Type) (α act test : Type)
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t]
    [∀ {β : Type}, PartialOrder (t β)] [∀ {β : Type}, OrderBot (t β)]
    [Linearizable t] :
    Monotone (lin_fin t α act test) :=
  Pomfin.lift_monotone Lpo.lin_mono

noncomputable def lin {t : Type → Type} {α act test : Type}
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)]
    [∀ {β : Type}, OrderBot (t β)]
    [Linearizable t]
    (p : Pom (Label act test)) : α → t α :=
  p.ext _ (lin_fin_monotone t α act test)

lemma lin_continuous {t : Type → Type} {α act test : Type}
    [Sem act α (t α)] [Sem test α (t Bool)] [Monad t]
    [ScottCompact (Label act test)]
    [∀ {β : Type}, OmegaCompletePartialOrder (t β)]
    [∀ {β : Type}, OrderBot (t β)]
    [Linearizable t] :
    ωScottContinuous (Pom.lin : Pom (Label act test) → α → t α) :=
  ext_continuous (lin_fin_monotone t α act test)

end Pom
