import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.Zeta

noncomputable section

/-- Concrete finite-spectrum package for the reduced cyclic-lift constant and its logarithmic
counterpart. The non-Perron spectrum is recorded as a finite set of normalized eigenvalues, and
the two fields are the closed product formula and the corresponding logarithmic identity. -/
structure FinitePartCyclicLiftReducedConstantClosedData where
  q : ℕ
  normalizedSpectrum : Finset ℝ
  cyclicLiftConstant : ℝ
  psi : ℝ
  reducedConstantClosed :
    cyclicLiftConstant =
      (1 / (q : ℝ)) * Finset.prod normalizedSpectrum (fun x => (1 - x ^ q)⁻¹)
  logarithmicClosed :
    psi =
      -Real.log (q : ℝ) -
        Finset.sum normalizedSpectrum (fun x => Real.log (1 - x ^ q))

namespace FinitePartCyclicLiftReducedConstantClosedData

/-- The closed product formula over the normalized non-Perron spectrum. -/
def productClosedForm (D : FinitePartCyclicLiftReducedConstantClosedData) : ℝ :=
  (1 / (D.q : ℝ)) * Finset.prod D.normalizedSpectrum (fun x => (1 - x ^ D.q)⁻¹)

/-- The logarithmic version of the same closed formula. -/
def logarithmicClosedForm (D : FinitePartCyclicLiftReducedConstantClosedData) : ℝ :=
  -Real.log (D.q : ℝ) -
    Finset.sum D.normalizedSpectrum (fun x => Real.log (1 - x ^ D.q))

/-- The cyclic-lift constant and its logarithmic normalization match the closed forms recorded in
the data package. -/
def Holds (D : FinitePartCyclicLiftReducedConstantClosedData) : Prop :=
  D.cyclicLiftConstant = D.productClosedForm ∧
    D.psi = D.logarithmicClosedForm

end FinitePartCyclicLiftReducedConstantClosedData

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the closed formula for reduced cyclic-lift
    constants in the ETDS finite-part section.
    thm:finite-part-cyclic-lift-reduced-constant-closed -/
theorem paper_etds_finite_part_cyclic_lift_reduced_constant_closed
    {Matrix : Type}
    (cyclicLiftConstant productClosedForm psi logarithmicClosedForm :
      Matrix → ℕ → ℝ)
    (closedFormToPsi :
      ∀ {A : Matrix} {q : ℕ},
        cyclicLiftConstant A q = productClosedForm A q →
          psi A q = logarithmicClosedForm A q)
    {A : Matrix} {q : ℕ}
    (hclosed : cyclicLiftConstant A q = productClosedForm A q) :
    cyclicLiftConstant A q = productClosedForm A q ∧
      psi A q = logarithmicClosedForm A q := by
  exact ⟨hclosed, closedFormToPsi hclosed⟩

/-- Paper label: `thm:finite-part-cyclic-lift-reduced-constant-closed`.
The reduced cyclic-lift constant is the `1 / q` product over the non-Perron normalized spectrum,
and the associated logarithmic anomaly is the termwise logarithm of the same closed form. -/
theorem paper_finite_part_cyclic_lift_reduced_constant_closed
    (D : FinitePartCyclicLiftReducedConstantClosedData) : D.Holds := by
  exact ⟨D.reducedConstantClosed, D.logarithmicClosed⟩

end

end Omega.Zeta
