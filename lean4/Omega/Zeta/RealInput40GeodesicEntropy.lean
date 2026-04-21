import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.RingTheory.Polynomial.Basic

namespace Omega.Zeta

/-- The degree-15 characteristic polynomial whose largest real root is the real-input-40
non-backtracking Perron value. -/
noncomputable def realInput40GeodesicEntropyPolynomial : Polynomial ℝ :=
  Polynomial.X ^ 15 - 4 * Polynomial.X ^ 12 - 9 * Polynomial.X ^ 11 - 12 * Polynomial.X ^ 10 -
    16 * Polynomial.X ^ 9 - 11 * Polynomial.X ^ 8 - 11 * Polynomial.X ^ 7 -
    4 * Polynomial.X ^ 6 - Polynomial.X ^ 5 + 8 * Polynomial.X ^ 4 + 12 * Polynomial.X ^ 3 +
    10 * Polynomial.X ^ 2 + 8 * Polynomial.X + 2

/-- Audited Perron-root data for the real-input-40 geodesic entropy package. -/
structure RealInput40GeodesicEntropyData where
  rhoNB : ℝ
  entropyNB : ℝ
  rootWitness : realInput40GeodesicEntropyPolynomial.eval rhoNB = 0
  maximalityWitness :
    ∀ x : ℝ, realInput40GeodesicEntropyPolynomial.eval x = 0 → x ≤ rhoNB
  entropyWitness : entropyNB = Real.log rhoNB

/-- The audited Perron value is a largest real root of the degree-15 polynomial. -/
def RealInput40GeodesicEntropyData.isLargestRealRoot
    (D : RealInput40GeodesicEntropyData) : Prop :=
  realInput40GeodesicEntropyPolynomial.eval D.rhoNB = 0 ∧
    ∀ x : ℝ, realInput40GeodesicEntropyPolynomial.eval x = 0 → x ≤ D.rhoNB

/-- The geodesic entropy is the logarithm of the non-backtracking Perron root.
    cor:real-input-40-geodesic-entropy -/
theorem paper_real_input_40_geodesic_entropy (D : RealInput40GeodesicEntropyData) :
    D.isLargestRealRoot ∧ D.entropyNB = Real.log D.rhoNB := by
  exact ⟨⟨D.rootWitness, D.maximalityWitness⟩, D.entropyWitness⟩

end Omega.Zeta
