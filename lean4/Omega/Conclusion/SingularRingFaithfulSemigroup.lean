import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.UnitCirclePhaseArithmetic.LeyangChebyshevSemiconjugacy

namespace Omega.Conclusion

open Omega.UnitCirclePhaseArithmetic

/-- Concrete normalization seed for the singular-ring rational-map package. -/
structure SingularRingFaithfulSemigroupData where
  normalizationConstant : ℂ := 1

namespace SingularRingFaithfulSemigroupData

/-- The normalized numerator is the `n`th Lee--Yang power map. -/
def normalizedNumerator (_D : SingularRingFaithfulSemigroupData) (n : ℕ) (z : ℂ) : ℂ :=
  z ^ n

/-- The denominator is already normalized to `1`. -/
def normalizedDenominator (_D : SingularRingFaithfulSemigroupData) (_n : ℕ) (_z : ℂ) : ℂ :=
  1

/-- The resulting rational self-map on the trace coordinate. -/
def rationalMap (D : SingularRingFaithfulSemigroupData) (n : ℕ) : ℂ → ℂ :=
  fun z => D.normalizedNumerator n z

/-- The normalized numerator/denominator presentation has degree exactly `n`. -/
def normalizedDegree (_D : SingularRingFaithfulSemigroupData) (n : ℕ) : ℕ :=
  n

/-- The Lee--Yang maps compose multiplicatively. -/
def semigroupLaw (D : SingularRingFaithfulSemigroupData) : Prop :=
  ∀ m n, 1 ≤ m → 1 ≤ n → Function.comp (D.rationalMap m) (D.rationalMap n) = D.rationalMap (m * n)

/-- Equality of normalized rational maps forces equality of normalized degrees, hence of the
indices. -/
def faithful (D : SingularRingFaithfulSemigroupData) : Prop :=
  ∀ m n, D.rationalMap m = D.rationalMap n → D.normalizedDegree m = D.normalizedDegree n ∧ m = n

lemma semigroupLaw_true (D : SingularRingFaithfulSemigroupData) : D.semigroupLaw := by
  intro m n hm hn
  simpa [rationalMap, normalizedNumerator, leyangFn] using
    (paper_leyang_chebyshev_semiconjugacy m n hm hn).2

lemma index_eq_of_rationalMap_eq (D : SingularRingFaithfulSemigroupData) {m n : ℕ}
    (hMaps : D.rationalMap m = D.rationalMap n) : m = n := by
  have hAt : (2 : ℂ) ^ m = (2 : ℂ) ^ n := by
    simpa [rationalMap, normalizedNumerator] using
      congrArg (fun f : ℂ → ℂ => f (2 : ℂ)) hMaps
  have hNatCast : (((2 ^ m : ℕ) : ℂ) = ((2 ^ n : ℕ) : ℂ)) := by
    simpa using hAt
  have hNat : 2 ^ m = 2 ^ n := by
    exact_mod_cast hNatCast
  exact Nat.pow_right_injective (by decide) hNat

lemma faithful_true (D : SingularRingFaithfulSemigroupData) : D.faithful := by
  intro m n hMaps
  have hmn : m = n := D.index_eq_of_rationalMap_eq hMaps
  refine ⟨?_, hmn⟩
  simp [normalizedDegree, hmn]

end SingularRingFaithfulSemigroupData

open SingularRingFaithfulSemigroupData

/-- Paper label: `thm:conclusion-singular-ring-faithful-semigroup`. The Lee--Yang
semiconjugacy package gives the multiplicative composition law, and the normalized degree of the
monomial numerator detects the index faithfully. -/
theorem paper_conclusion_singular_ring_faithful_semigroup (D : SingularRingFaithfulSemigroupData) :
    D.semigroupLaw ∧ D.faithful := by
  exact ⟨D.semigroupLaw_true, D.faithful_true⟩

end Omega.Conclusion
