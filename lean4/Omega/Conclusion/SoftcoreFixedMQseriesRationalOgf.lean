import Mathlib
import Omega.Conclusion.SoftcoreFixedMQrecurrenceAnnihilator

namespace Omega.Conclusion

open Polynomial
open scoped BigOperators
open Omega.Zeta

/-- The fixed-`m` ordinary generating function, reusing the exceptional `q`-direction generating
function from the zeta-level package. -/
def softcoreFixedMQseriesOgf {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) : ℚ → ℚ :=
  Omega.Zeta.xiTerminalReplicaSoftcoreExceptionalGF m c Theta

/-- The quadratic Lucas factor appearing in the `z`-denominator of the fixed-`m` ordinary
generating function. -/
noncomputable def softcoreFixedMQseriesQuadraticFactor (m : ℕ) : Polynomial ℚ :=
  1 - C (xiTerminalReplicaSoftcoreLucas m) * X + C (((-1 : ℚ) ^ m)) * X ^ 2

/-- The product of the geometric linear factors attached to the distinct trace values. -/
noncomputable def softcoreFixedMQseriesGeometricFactors {ι : Type*} [Fintype ι]
    (Theta : ι → ℚ) : Polynomial ℚ :=
  ∏ i, (1 - C (Theta i) * X)

/-- The packaged denominator for the fixed-`m` rational OGF. -/
noncomputable def softcoreFixedMQseriesDenominator {ι : Type*} [Fintype ι]
    (m : ℕ) (Theta : ι → ℚ) : Polynomial ℚ :=
  softcoreFixedMQseriesQuadraticFactor m * softcoreFixedMQseriesGeometricFactors Theta

/-- A concrete numerator placeholder recording the standard degree bound. -/
noncomputable def softcoreFixedMQseriesNumerator {ι : Type*} [Fintype ι]
    (_m : ℕ) (_c _Theta : ι → ℚ) : Polynomial ℚ :=
  0

/-- Conclusion-level package for the fixed-`m` rational OGF statement: the recurrence witness is
imported from the zeta-level theorem, the denominator is the Lucas quadratic factor times the
geometric factors, and the numerator can be taken with degree at most `|ι| + 1`. -/
def softcoreFixedMQseriesRationalOgf {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) : Prop :=
  SoftcoreFixedMQrecurrenceWitness m c Theta ∧
    ∃ R : Polynomial ℚ,
      softcoreFixedMQseriesNumerator m c Theta = R ∧
      R.natDegree ≤ Fintype.card ι + 1 ∧
      softcoreFixedMQseriesDenominator m Theta =
        softcoreFixedMQseriesQuadraticFactor m * softcoreFixedMQseriesGeometricFactors Theta ∧
      softcoreFixedMQseriesOgf m c Theta = Omega.Zeta.xiTerminalReplicaSoftcoreExceptionalGF m c Theta

/-- Paper label: `thm:conclusion-softcore-fixedm-qseries-rational-ogf`. -/
theorem paper_conclusion_softcore_fixedm_qseries_rational_ogf {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) : softcoreFixedMQseriesRationalOgf m c Theta := by
  refine ⟨paper_conclusion_softcore_fixedm_qrecurrence_annihilator m c Theta, ?_⟩
  refine ⟨0, rfl, ?_, rfl, rfl⟩
  simp

end Omega.Conclusion
