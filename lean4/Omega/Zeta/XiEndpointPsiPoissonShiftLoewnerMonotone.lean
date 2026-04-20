import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.Zeta.XiEndpointJensenDefectH12GramKernel

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite data for a Poisson-shifted endpoint Gram model. The parameter `decay j`
records the nonnegative spectral decay attached to the `j`th endpoint mode, while
`amplitude j` records its coefficient in the tested quadratic form. -/
structure XiEndpointPsiPoissonShiftLoewnerMonotoneData where
  J : ℕ
  decay : Fin J → ℝ
  amplitude : Fin J → ℝ
  decay_nonneg : ∀ j, 0 ≤ decay j

namespace XiEndpointPsiPoissonShiftLoewnerMonotoneData

/-- The individual Poisson-shifted Gram contribution of the `j`th mode. -/
noncomputable def gramTerm (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData)
    (t : ℝ) (m : Fin D.J → ℝ) (j : Fin D.J) : ℝ :=
  (m j * D.amplitude j) ^ 2 * Real.exp (t * (-2 * D.decay j))

/-- The tested quadratic form of the finite Poisson-shifted Gram model. -/
noncomputable def quadraticForm (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData)
    (t : ℝ) (m : Fin D.J → ℝ) : ℝ :=
  ∑ j, D.gramTerm t m j

/-- The explicit dissipative derivative proxy for the Poisson-shifted Gram form. -/
noncomputable def dissipativeDerivative (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData)
    (t : ℝ) (m : Fin D.J → ℝ) : ℝ :=
  -2 * ∑ j, (m j * D.amplitude j) ^ 2 * D.decay j * Real.exp (t * (-2 * D.decay j))

/-- Package form of the Loewner monotonicity and the nonpositive dissipative derivative for the
finite exponential-weighted surrogate of the Poisson-shifted endpoint Gram kernel. -/
def monotoneLaw (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData) : Prop :=
  (∀ ⦃t₁ t₂ : ℝ⦄, 0 ≤ t₁ → t₁ ≤ t₂ →
      ∀ m : Fin D.J → ℝ, D.quadraticForm t₂ m ≤ D.quadraticForm t₁ m) ∧
    ∀ t : ℝ, 0 ≤ t →
      ∀ m : Fin D.J → ℝ,
        D.dissipativeDerivative t m =
            -2 * ∑ j, (m j * D.amplitude j) ^ 2 * D.decay j * Real.exp (t * (-2 * D.decay j)) ∧
          D.dissipativeDerivative t m ≤ 0

end XiEndpointPsiPoissonShiftLoewnerMonotoneData

/-- The concrete Poisson-shifted endpoint Gram surrogate is Loewner monotone in the shift
parameter, and its explicit dissipative derivative is nonpositive.
    thm:xi-endpoint-psi-poisson-shift-loewner-monotone -/
theorem paper_xi_endpoint_psi_poisson_shift_loewner_monotone
    (D : XiEndpointPsiPoissonShiftLoewnerMonotoneData) : D.monotoneLaw := by
  let _ := paper_xi_endpoint_jensen_defect_h12_gram_kernel
  refine ⟨?_, ?_⟩
  · intro t₁ t₂ _ ht m
    unfold XiEndpointPsiPoissonShiftLoewnerMonotoneData.quadraticForm
    refine Finset.sum_le_sum ?_
    intro j hj
    have hsq : 0 ≤ (m j * D.amplitude j) ^ 2 := sq_nonneg _
    have hexp :
        Real.exp (t₂ * (-2 * D.decay j)) ≤ Real.exp (t₁ * (-2 * D.decay j)) := by
      apply Real.exp_le_exp.mpr
      nlinarith [D.decay_nonneg j, ht]
    exact mul_le_mul_of_nonneg_left hexp hsq
  · intro t _ m
    refine ⟨rfl, ?_⟩
    have hsum_nonneg :
        0 ≤ ∑ j, (m j * D.amplitude j) ^ 2 * D.decay j * Real.exp (t * (-2 * D.decay j)) := by
      refine Finset.sum_nonneg ?_
      intro j hj
      refine mul_nonneg (mul_nonneg (sq_nonneg _) (D.decay_nonneg j)) ?_
      exact le_of_lt (Real.exp_pos _)
    unfold XiEndpointPsiPoissonShiftLoewnerMonotoneData.dissipativeDerivative
    nlinarith

end Omega.Zeta
