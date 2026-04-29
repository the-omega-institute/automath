import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The endpoint-log form obtained by integrating the bandpass Poisson kernel in the vertical
variable. -/
noncomputable def xiLogdefectBandpassScalar (x gamma y0 y1 : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log (((x - gamma) ^ 2 + y1 ^ 2) / ((x - gamma) ^ 2 + y0 ^ 2))

/-- The primitive whose endpoint difference produces the scalar bandpass logarithm. -/
noncomputable def xiLogdefectPoissonPrimitive (x gamma y : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((x - gamma) ^ 2 + y ^ 2)

/-- Finite weighted log-defect bandpass potential. -/
noncomputable def xiLogdefectBandpassPotential
    {n : ℕ} (x y0 y1 : ℝ) (center weight : Fin n → ℝ) : ℝ :=
  ∑ i, weight i * xiLogdefectBandpassScalar x (center i) y0 y1

/-- Finite weighted Poisson-primitive decomposition attached to the same defect data. -/
noncomputable def xiLogdefectBandpassPoissonDecomposition
    {n : ℕ} (x y0 y1 : ℝ) (center weight : Fin n → ℝ) : ℝ :=
  ∑ i, weight i *
    (xiLogdefectPoissonPrimitive x (center i) y1 -
      xiLogdefectPoissonPrimitive x (center i) y0)

/-- The `y`-slice weights used in the finite Poisson decomposition. -/
def xiLogdefectBandpassSigma
    {n : ℕ} (weight : Fin n → ℝ) : Fin n → ℝ :=
  weight

lemma xiLogdefectBandpassScalar_eq_primitive_difference
    (x gamma y0 y1 : ℝ) (hy0 : 0 < y0) (hy1 : 0 < y1) :
    xiLogdefectBandpassScalar x gamma y0 y1 =
      xiLogdefectPoissonPrimitive x gamma y1 - xiLogdefectPoissonPrimitive x gamma y0 := by
  have hden : 0 < (x - gamma) ^ 2 + y0 ^ 2 := by positivity
  have hnum : 0 < (x - gamma) ^ 2 + y1 ^ 2 := by positivity
  unfold xiLogdefectBandpassScalar xiLogdefectPoissonPrimitive
  rw [Real.log_div hnum.ne' hden.ne']
  ring

/-- Finite Tonelli-Fubini reduction of the bandpass logarithmic defect to a Poisson-primitive
decomposition.
`thm:xi-logdefect-bandpass-poisson-representation` -/
theorem paper_xi_logdefect_bandpass_poisson_representation
    {n : ℕ} (x y0 y1 : ℝ) (center weight : Fin n → ℝ) (hy0 : 0 < y0) (hy1 : 0 < y1) :
    xiLogdefectBandpassPotential x y0 y1 center (xiLogdefectBandpassSigma weight) =
      xiLogdefectBandpassPoissonDecomposition x y0 y1 center weight := by
  unfold xiLogdefectBandpassPotential xiLogdefectBandpassPoissonDecomposition
    xiLogdefectBandpassSigma
  refine Finset.sum_congr rfl ?_
  intro i hi
  rw [xiLogdefectBandpassScalar_eq_primitive_difference x (center i) y0 y1 hy0 hy1]

end Omega.Zeta
