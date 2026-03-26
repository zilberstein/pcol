import Pcol.Semantics.Lpo.Basic
import Pcol.Semantics.Lpo.Order
import Pcol.Semantics.Lpo.Iso2

def Pom (l : Type) [Bot l] : Type := Quotient (@Lpo.instSetoid l _)

instance {l : Type} [LE l] [Bot l] : LE (Pom l) where
  le p q := ∃ a b, a ≤ b ∧ p = Quotient.mk' a ∧ q = Quotient.mk' b

namespace Pom

lemma le_iff_1 {l : Type} [Bot l] [LE l] {p q : Pom l} :
  p ≤ q ↔ ∀ a, p = Quotient.mk' a → ∃ b, q = Quotient.mk' b ∧ a ≤ b := by {
  constructor
  · intro hle a ha; rcases hle with ⟨a', b', hab, ha', hb'⟩
    rw [ha] at ha'
    rcases Quotient.eq.1 ha' with ⟨e, hperm⟩
    -- b should be b' premuted by the inverse of f, then the rest is
    -- pretty easy, assuming we have a lemms that
    -- a ≤ b ↔ a.permute f ≤ b.premute f
    sorry
  · sorry
}

lemma le_iff_2 {l : Type} [Bot l] [LE l] {p q : Pom l} :
  p ≤ q ↔ ∀ b, q = Quotient.mk' b → ∃ a, p = Quotient.mk' a ∧ a ≤ b := by {
    sorry
  }

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

instance {l : Type} [PartialOrder l] [OrderBot l] : Preorder (Pom l) where
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

instance {l : Type} [PartialOrder l] [OrderBot l] : PartialOrder (Pom l) where
  le_antisymm p q hpq hqp := by
    obtain ⟨α, β, hle, rfl, rfl⟩ := hpq
    obtain ⟨α', heq, hle'⟩ := Pom.le_iff_1.mp hqp β rfl
    sorry
