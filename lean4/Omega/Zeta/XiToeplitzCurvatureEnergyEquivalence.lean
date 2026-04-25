import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.Zeta.XiToeplitzPrincipalMinorDiscreteCurvatureRecovery

namespace Omega.Zeta

open scoped BigOperators
open XiToeplitzDetVerblunskyData

noncomputable section

/-- The Verblunsky `ℓ²` energy density at level `n`. -/
def xi_toeplitz_curvature_energy_equivalence_reflectionEnergy
    (D : XiToeplitzDetVerblunskyData) (n : ℕ) : ℝ :=
  |D.alphaAt n| ^ 2

/-- The logarithmic discrete-curvature energy at level `n`. -/
def xi_toeplitz_curvature_energy_equivalence_curvatureEnergy
    (D : XiToeplitzDetVerblunskyData) (n : ℕ) : ℝ :=
  -Real.log (1 - xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D n)

lemma xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_tail
    (D : XiToeplitzDetVerblunskyData) :
    ∀ n : ℕ,
      xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D (n + D.steps) = 0 := by
  intro n
  unfold xi_toeplitz_curvature_energy_equivalence_reflectionEnergy
  unfold XiToeplitzDetVerblunskyData.alphaAt
  have hnot : ¬ n + D.steps < D.steps := by omega
  simp [hnot]

lemma xi_toeplitz_curvature_energy_equivalence_curvatureEnergy_tail
    (D : XiToeplitzDetVerblunskyData) :
    ∀ n : ℕ, xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D (n + D.steps) = 0 := by
  intro n
  unfold xi_toeplitz_curvature_energy_equivalence_curvatureEnergy
  rw [xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_tail D n]
  norm_num

lemma xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_summable
    (D : XiToeplitzDetVerblunskyData) :
    Summable (xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D) := by
  have htail :
      Summable (fun n : ℕ =>
        xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D (n + D.steps)) := by
    simpa [xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_tail D] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  exact (summable_nat_add_iff D.steps).1 htail

lemma xi_toeplitz_curvature_energy_equivalence_curvatureEnergy_summable
    (D : XiToeplitzDetVerblunskyData) :
    Summable (xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D) := by
  have htail :
      Summable (fun n : ℕ =>
        xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D (n + D.steps)) := by
    simpa [xi_toeplitz_curvature_energy_equivalence_curvatureEnergy_tail D] using
      (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  exact (summable_nat_add_iff D.steps).1 htail

/-- Paper label: `prop:xi-toeplitz-curvature-energy-equivalence`. In the finite Toeplitz
determinant model, the discrete curvature is exactly `1 - |α_n|²` on the good prefix and both the
`ℓ²` Verblunsky energy and the logarithmic curvature energy are eventually zero beyond that
prefix; therefore the two summability conditions are equivalent. -/
theorem paper_xi_toeplitz_curvature_energy_equivalence
    (D : XiToeplitzDetVerblunskyData)
    (hgood : ∀ n < D.steps, |D.alphaAt n| < 1) :
    (∀ n < D.steps,
      D.discreteCurvature n =
        1 - xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D n) ∧
      (∀ n : ℕ,
        xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D (n + D.steps) = 0 ∧
          xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D (n + D.steps) = 0) ∧
      (Summable (xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D) ↔
        Summable (xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    rw [D.discreteCurvature_eq_one_sub_abs_sq hgood hn]
    rfl
  · intro n
    exact ⟨xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_tail D n,
      xi_toeplitz_curvature_energy_equivalence_curvatureEnergy_tail D n⟩
  · have hreflection :
      Summable (xi_toeplitz_curvature_energy_equivalence_reflectionEnergy D) :=
        xi_toeplitz_curvature_energy_equivalence_reflectionEnergy_summable D
    have hcurvature :
      Summable (xi_toeplitz_curvature_energy_equivalence_curvatureEnergy D) :=
        xi_toeplitz_curvature_energy_equivalence_curvatureEnergy_summable D
    constructor <;> intro _ <;> assumption

end

end Omega.Zeta
