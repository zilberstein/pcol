import Mathlib
import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.Isomorphism

def Pom (l : Type) [Bot l] : Type := Quotient (@Lpo.instSetoid l _)

instance {l : Type} [LE l] [Bot l] : LE (Pom l) where
  le p q := ∃ a b, a ≤ b ∧ p = Quotient.mk' a ∧ q = Quotient.mk' b

namespace Pom
-- lemma le_iff_exists_exists {l : Type} [Bot l] [LE l] {p q : Pom l} :
--   p ≤ q ↔ ∃ a ∈ p, ∃ b ∈ q, a ≤ b := by {
--     constructor
--     · intro hpq; rcases p with ⟨s, a, ha, _⟩
--       exact ⟨a, ha, hpq a ha⟩
--     · intro ⟨a, ha, hle⟩ a' ha'
--       rcases p with ⟨s, b, hb, hiso⟩
--       -- Need to prove that IsIsomorphic is an eqivalence relation
--       sorry
--   }

-- lemma le_iff_forall_exists {l : Type} [Bot l] [LE l] {p q : Pom l} :
--   p ≤ q ↔ ∃ b ∈ q, ∃ a ∈ p, a ≤ b := by sorry

def singleton {l : Type} [Bot l] (ℓ : l) : Pom l :=
  Quotient.mk' (Lpo.singleton default ℓ)

end Pom

instance {l : Type} [Bot l] : Bot (Pom l) where
  bot := Pom.singleton ⊥

instance {l : Type} [LE l] [OrderBot l] : OrderBot (Pom l) where
  bot_le p := by {
    rcases Quotient.exists_rep p with ⟨a, ha⟩
    rcases a.property.rel.single_rooted with ⟨x, hnodes⟩
    refine ⟨Lpo.singleton x ⊥, a, ?_, ?_, ?_⟩
    · have hx : x ∈ a.nodes := by sorry
      constructor
      · simp [Lpo.singleton, Lpo.nodes]; exact hx
      · simp [Lpo.singleton, Lpo.nodes]; intro y hx z; sorry
      · sorry
      · sorry
      · sorry
      · sorry
    · simp [Bot.bot, Pom.singleton]; refine Quotient.sound ?_
      sorry
    · rw [← ha]; rfl
  }

instance {l : Type} [Preorder l] [Bot l] : Preorder (Pom l) where
  le_refl p := by
    rcases Quotient.exists_rep p with ⟨a, ha⟩
    exact ⟨a, a, le_refl a, Eq.symm ha, Eq.symm ha⟩

  le_trans p q r := by {
    intro ⟨a, b, hab, hpa, hqb⟩ ⟨c, d, hcd, hqc, hrd⟩
    rw [hqb] at hqc; have heq := Quotient.exact hqc
    -- Need to prove that if a ≤ b and b ≈ c and b ≤ c, then there exists
    -- d such that c ≈ d and b ≤ d
    sorry
  }

instance {l : Type} [PartialOrder l] [Bot l] : PartialOrder (Pom l) where
  le_antisymm p q hpq hqp := by sorry
