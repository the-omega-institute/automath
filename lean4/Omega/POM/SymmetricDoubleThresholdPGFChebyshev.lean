import Mathlib.Tactic

namespace Omega.POM

/-- Concrete threshold/step parameter package for the symmetric double-threshold PGF closed form.
The threshold `T` is finite and the generating parameter `z` is rational, so the two advertised
closed forms can be compared by explicit denominator algebra. -/
structure SymmetricDoubleThresholdPGFChebyshevData where
  T : ℕ
  z : ℚ

namespace SymmetricDoubleThresholdPGFChebyshevData

/-- The denominator obtained from the finite-interval Chebyshev recurrence normalization. -/
def chebyshevDenominator (D : SymmetricDoubleThresholdPGFChebyshevData) : ℚ :=
  (D.T + 1 : ℚ) - D.T * D.z

/-- The same denominator written through the characteristic-root normalization. -/
def rootDenominator (D : SymmetricDoubleThresholdPGFChebyshevData) : ℚ :=
  1 + D.T * (1 - D.z)

lemma rootDenominator_eq_chebyshevDenominator (D : SymmetricDoubleThresholdPGFChebyshevData) :
    D.rootDenominator = D.chebyshevDenominator := by
  unfold rootDenominator chebyshevDenominator
  ring

/-- Closed form obtained by imposing the `±T` boundary data on the Chebyshev normalization. -/
def chebyshevClosedForm (D : SymmetricDoubleThresholdPGFChebyshevData) : ℚ :=
  D.z / D.chebyshevDenominator

/-- The same closed form written through the characteristic roots. -/
def rootClosedForm (D : SymmetricDoubleThresholdPGFChebyshevData) : ℚ :=
  D.z / D.rootDenominator

/-- The threshold-hitting PGF evaluated at the origin state. -/
def pgfAtZero (D : SymmetricDoubleThresholdPGFChebyshevData) : ℚ :=
  D.z / D.chebyshevDenominator

end SymmetricDoubleThresholdPGFChebyshevData

/-- Paper label: `thm:pom-symmetric-double-threshold-pgf-chebyshev`. -/
theorem paper_pom_symmetric_double_threshold_pgf_chebyshev
    (D : SymmetricDoubleThresholdPGFChebyshevData) :
    D.pgfAtZero = D.chebyshevClosedForm ∧ D.pgfAtZero = D.rootClosedForm := by
  refine ⟨rfl, ?_⟩
  simp [SymmetricDoubleThresholdPGFChebyshevData.pgfAtZero,
    SymmetricDoubleThresholdPGFChebyshevData.rootClosedForm,
    SymmetricDoubleThresholdPGFChebyshevData.rootDenominator_eq_chebyshevDenominator]

end Omega.POM
