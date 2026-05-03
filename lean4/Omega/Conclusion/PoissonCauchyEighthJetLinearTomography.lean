import Mathlib.Data.Real.Basic
import Mathlib.Data.Matrix.Basic

namespace Omega.Conclusion

noncomputable section

open BigOperators Matrix

/-- Concrete eighth-jet tomography data: moments of the centered measure, a `3 × 3` matrix whose
rows are the second, third, and fourth generator jets, and the three observed eighth coefficients.
The injectivity field records invertibility of that jet matrix as the usable linear-algebra
hypothesis. -/
structure conclusion_poisson_cauchy_eighth_jet_linear_tomography_data where
  mu2 : ℝ
  mu3 : ℝ
  mu4 : ℝ
  mu5 : ℝ
  mu6 : ℝ
  jetMatrix : Matrix (Fin 3) (Fin 3) ℝ
  coefficient8 : Fin 3 → ℝ
  coefficient_formula :
    ∀ i : Fin 3,
      512 * coefficient8 i =
        ∑ j : Fin 3,
          jetMatrix i j *
            (if j = 0 then 24 * mu2 * mu6 - 60 * mu3 * mu5 + 40 * mu4 ^ 2
             else if j = 1 then 24 * mu2 ^ 2 * mu4 - 18 * mu2 * mu3 ^ 2
             else 3 * mu2 ^ 4)
  jetMatrix_injective :
    ∀ v w : Fin 3 → ℝ,
      (∀ i : Fin 3, (∑ j : Fin 3, jetMatrix i j * v j) =
        ∑ j : Fin 3, jetMatrix i j * w j) → v = w

/-- The three-component moment--jet vector appearing in the eighth-order coefficient. -/
def conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet
    (D : conclusion_poisson_cauchy_eighth_jet_linear_tomography_data) (j : Fin 3) : ℝ :=
  if j = 0 then 24 * D.mu2 * D.mu6 - 60 * D.mu3 * D.mu5 + 40 * D.mu4 ^ 2
  else if j = 1 then 24 * D.mu2 ^ 2 * D.mu4 - 18 * D.mu2 * D.mu3 ^ 2
  else 3 * D.mu2 ^ 4

/-- Dot product of one generator-jet row with a candidate three-component moment vector. -/
def conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot
    (D : conclusion_poisson_cauchy_eighth_jet_linear_tomography_data)
    (i : Fin 3) (v : Fin 3 → ℝ) : ℝ :=
  ∑ j : Fin 3, D.jetMatrix i j * v j

/-- The coefficient formula as a dot product, plus uniqueness of the recovered moment--jet vector
from the three eighth-order coefficients. -/
def conclusion_poisson_cauchy_eighth_jet_linear_tomography_conclusion
    (D : conclusion_poisson_cauchy_eighth_jet_linear_tomography_data) : Prop :=
  (∀ i : Fin 3,
    512 * D.coefficient8 i =
      conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot D i
        (conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet D)) ∧
  (∀ v : Fin 3 → ℝ,
    (∀ i : Fin 3,
      conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot D i v =
        512 * D.coefficient8 i) →
      v = conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet D)

/-- Paper label: `thm:conclusion-poisson-cauchy-eighth-jet-linear-tomography`. -/
theorem paper_conclusion_poisson_cauchy_eighth_jet_linear_tomography
    (D : conclusion_poisson_cauchy_eighth_jet_linear_tomography_data) :
    conclusion_poisson_cauchy_eighth_jet_linear_tomography_conclusion D := by
  constructor
  · intro i
    simpa [
      conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot,
      conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet]
      using D.coefficient_formula i
  · intro v hv
    apply D.jetMatrix_injective
    intro i
    calc
      (∑ j : Fin 3, D.jetMatrix i j * v j)
          = 512 * D.coefficient8 i := by
            simpa [conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot] using hv i
      _ = ∑ j : Fin 3, D.jetMatrix i j *
            conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet D j := by
            simpa [
              conclusion_poisson_cauchy_eighth_jet_linear_tomography_dot,
              conclusion_poisson_cauchy_eighth_jet_linear_tomography_momentJet]
              using D.coefficient_formula i

end

end Omega.Conclusion
