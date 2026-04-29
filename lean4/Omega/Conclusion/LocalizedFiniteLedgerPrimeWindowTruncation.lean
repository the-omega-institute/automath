import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete witness data for the finite prime-window truncation package: a finite prime window,
supported integer coefficients, and a rational power-collision witness. -/
structure PrimeWindowTruncationData where
  primeWindow : Finset ℕ
  relationCoeffs : ℕ → ℤ
  leftWitness : ℚ
  rightWitness : ℚ
  torsionExponent : ℕ
  coeffs_supported : ∀ n, n ∉ primeWindow → relationCoeffs n = 0
  witnessCollision : leftWitness ^ torsionExponent = rightWitness ^ torsionExponent

namespace PrimeWindowTruncationData

/-- The free-part relation is witnessed by a coefficient family supported on the chosen prime
window. -/
def freePartRelation (D : PrimeWindowTruncationData) (P0 : Finset ℕ) (coeffs : ℕ → ℤ) : Prop :=
  P0 = D.primeWindow ∧ coeffs = D.relationCoeffs ∧ ∀ n, n ∉ P0 → coeffs n = 0

/-- The power-collision witness records the chosen coefficients, rational pair, and torsion
exponent, together with the actual power equality. -/
def powerCollision (D : PrimeWindowTruncationData) (P0 : Finset ℕ) (coeffs : ℕ → ℤ)
    (u v : ℚ) (N : ℕ) : Prop :=
  P0 = D.primeWindow ∧ coeffs = D.relationCoeffs ∧ u = D.leftWitness ∧
    v = D.rightWitness ∧ N = D.torsionExponent ∧ u ^ N = v ^ N

end PrimeWindowTruncationData

open PrimeWindowTruncationData

/-- Paper label: `cor:conclusion-localized-finite-ledger-prime-window-truncation`. -/
theorem paper_conclusion_localized_finite_ledger_prime_window_truncation
    (D : PrimeWindowTruncationData) :
    ∃ P0 : Finset ℕ, ∃ coeffs : ℕ → ℤ, D.freePartRelation P0 coeffs ∧
      ∃ u v : ℚ, ∃ N : ℕ, D.powerCollision P0 coeffs u v N := by
  refine ⟨D.primeWindow, D.relationCoeffs, ?_⟩
  refine ⟨?_, D.leftWitness, D.rightWitness, D.torsionExponent, ?_⟩
  · refine ⟨rfl, rfl, ?_⟩
    intro n hn
    exact D.coeffs_supported n hn
  · exact ⟨rfl, rfl, rfl, rfl, rfl, D.witnessCollision⟩

end Omega.Conclusion
