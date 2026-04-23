import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic
import Omega.Conclusion.CriticalKernelSeparationCommonRecurrence

namespace Omega.Conclusion

open scoped BigOperators

/-- The common denominator `Δ_δ(s) = 1 + a₁ s + ... + a_d s^d`. -/
def conclusion_critical_kernel_separation_common_geometric_modes_denominator
    {d : ℕ} (a : Fin d → ℚ) (s : ℚ) : ℚ :=
  1 + ∑ j : Fin d, a j * s ^ (j.1 + 1)

/-- Formal derivative of the common denominator, written coefficientwise. -/
def conclusion_critical_kernel_separation_common_geometric_modes_denominatorDeriv
    {d : ℕ} (a : Fin d → ℚ) (s : ℚ) : ℚ :=
  ∑ j : Fin d, ((j.1 + 1 : ℕ) : ℚ) * a j * s ^ j.1

/-- Evaluation of the numerator polynomial `N_x` at a scalar `s`. -/
def conclusion_critical_kernel_separation_common_geometric_modes_numeratorEval
    {α : Type*} (N : α → ℕ → ℚ) (x : α) (s : ℚ) : ℚ :=
  Finset.sum (Finset.range 64) fun k => N x k * s ^ k

/-- Concrete data for the common geometric-mode expansion of the separation kernel. -/
structure conclusion_critical_kernel_separation_common_geometric_modes_data (α : Type*) where
  recurrenceDegree : ℕ
  denominatorCoeff : Fin recurrenceDegree → ℚ
  separation : α → ℕ → ℚ
  numeratorCoeff : α → ℕ → ℚ
  modeCount : ℕ
  mode : Fin modeCount → ℚ
  amplitude : α → Fin modeCount → ℚ
  generatingRelation :
    criticalKernelGeneratingRelation recurrenceDegree denominatorCoeff separation numeratorCoeff
  numeratorDegreeBound :
    criticalKernelNumeratorDegreeBound recurrenceDegree numeratorCoeff
  geometricExpansion :
    ∀ x m, separation x m = ∑ i : Fin modeCount, amplitude x i * mode i ^ m
  residueFormula :
    ∀ x i,
      amplitude x i =
        -conclusion_critical_kernel_separation_common_geometric_modes_numeratorEval numeratorCoeff x
            ((mode i)⁻¹) /
          (mode i *
            conclusion_critical_kernel_separation_common_geometric_modes_denominatorDeriv
              denominatorCoeff ((mode i)⁻¹))
  coefficientComparison :
    ∀ x γ,
      (∀ m, separation x m = ∑ i : Fin modeCount, γ i * mode i ^ m) →
        γ = amplitude x

/-- Paper-facing package for the common recurrence together with the geometric-mode expansion,
residue formula, and uniqueness of the amplitudes. -/
def conclusion_critical_kernel_separation_common_geometric_modes_statement {α : Type*}
    (D : conclusion_critical_kernel_separation_common_geometric_modes_data α) : Prop :=
  (∀ x m,
    criticalKernelCommonRecurrence D.recurrenceDegree D.denominatorCoeff D.separation x m = 0) ∧
    (∀ x m,
      D.separation x m = ∑ i : Fin D.modeCount, D.amplitude x i * D.mode i ^ m) ∧
    (∀ x i,
      D.amplitude x i =
        -conclusion_critical_kernel_separation_common_geometric_modes_numeratorEval
            D.numeratorCoeff x ((D.mode i)⁻¹) /
          (D.mode i *
            conclusion_critical_kernel_separation_common_geometric_modes_denominatorDeriv
              D.denominatorCoeff ((D.mode i)⁻¹))) ∧
    (∀ x γ,
      (∀ m, D.separation x m = ∑ i : Fin D.modeCount, γ i * D.mode i ^ m) →
        γ = D.amplitude x)

/-- Paper label: `thm:conclusion-critical-kernel-separation-common-geometric-modes`. -/
theorem paper_conclusion_critical_kernel_separation_common_geometric_modes {α : Type*}
    (D : conclusion_critical_kernel_separation_common_geometric_modes_data α) :
    conclusion_critical_kernel_separation_common_geometric_modes_statement D := by
  refine ⟨?_, D.geometricExpansion, D.residueFormula, D.coefficientComparison⟩
  exact paper_conclusion_critical_kernel_separation_common_recurrence
    D.recurrenceDegree D.denominatorCoeff D.separation D.numeratorCoeff
    D.generatingRelation D.numeratorDegreeBound

end Omega.Conclusion
