import Pcol.ConvexPowerset
import Pcol.ConvexPowerset.Monad
import Pcol.Semantics.Linearization

-- An instance for linearizing into the convex powerdomain
instance : Lin C where
  nondet {ι X} (f : ι → C X) :=
    bind ⟨(Set.univ : Set (Distr ι)), sorry⟩ f

  nondet_min p S₁ S₂ :=
    ⟨ ⋃ (q : ENNReal) (_ : q ≥ p) (hq : q ≤ 1), (convex_comb S₁.1 S₂.1 q hq)
    , sorry ⟩

instance : LawfulLin C where
  pure_mono := sorry
  nondet_mono := sorry
  nondet_min_mono := sorry
  bind_mono_left := sorry
  bind_mono_right := sorry
