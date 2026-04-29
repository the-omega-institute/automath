import Mathlib.Data.Nat.Totient
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiFoldCongruenceUnitalAutomorphismRigidity

namespace Omega.Zeta

/-- Concrete visible-arithmetic idempotent model for the fold-congruence quotient. -/
abbrev visibleArithmeticIdempotents (m : Nat) : Type :=
  foldCongruencePrimeSupportModel m

/-- Unit-count and visible-idempotent-count package for the fold-congruence arithmetic model.
    thm:xi-visible-arithmetic-unit-idempotent-count -/
theorem paper_xi_visible_arithmetic_unit_idempotent_count (m : Nat) :
    Fintype.card (Units (foldCongruenceSemiring m)) = Nat.totient (foldCongruenceModulus m) ∧
      Fintype.card (visibleArithmeticIdempotents m) = 2 ^ foldCongruencePrimeSupport m := by
  refine ⟨?_, ?_⟩
  · simpa [foldCongruenceSemiring, foldCongruenceModulus] using
      (ZMod.card_units_eq_totient (foldCongruenceModulus m))
  · simp [visibleArithmeticIdempotents, foldCongruencePrimeSupportModel]

end Omega.Zeta
