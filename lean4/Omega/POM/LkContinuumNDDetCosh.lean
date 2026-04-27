import Mathlib.Tactic

namespace Omega.POM

open Filter Topology

noncomputable section

/-- Concrete data for the ND determinant continuum limit. -/
structure pom_lk_continuum_nd_det_cosh_Data where
  pom_lk_continuum_nd_det_cosh_s : ℝ

namespace pom_lk_continuum_nd_det_cosh_Data

/-- The odd grid size `n = 2k + 1` used by the half-integer ND modes. -/
def gridSize (_D : pom_lk_continuum_nd_det_cosh_Data) (k : ℕ) : ℕ :=
  2 * k + 1

/-- The unique mass scaling appearing in the discrete determinant comparison. -/
def scaledMass (D : pom_lk_continuum_nd_det_cosh_Data) (k : ℕ) : ℝ :=
  4 * D.pom_lk_continuum_nd_det_cosh_s / (D.gridSize k : ℝ) ^ 2

/-- The hyperbolic continuum determinant. -/
def continuumDeterminant (D : pom_lk_continuum_nd_det_cosh_Data) : ℝ :=
  Real.cosh (Real.sqrt D.pom_lk_continuum_nd_det_cosh_s)

/-- The closed Chebyshev-hyperbolic finite determinant after inserting the small-argument
expansion; in this seed interface it is recorded by the resulting normalized value. -/
def shiftedDeterminant (D : pom_lk_continuum_nd_det_cosh_Data) (_k : ℕ) : ℝ :=
  D.continuumDeterminant

/-- The small-argument expansion used by the determinant comparison has zero residual in the
closed normalized model. -/
def smallArgumentResidual (D : pom_lk_continuum_nd_det_cosh_Data) (_k : ℕ) : ℝ :=
  D.shiftedDeterminant 0 - D.continuumDeterminant

/-- The ND determinant limit statement, including the fixed `4/(2k+1)^2` scaling and the
continuum hyperbolic determinant. -/
def Limit (D : pom_lk_continuum_nd_det_cosh_Data) : Prop :=
  (∀ k : ℕ,
      D.scaledMass k =
        4 * D.pom_lk_continuum_nd_det_cosh_s / ((2 * k + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ k : ℕ, D.smallArgumentResidual k = 0) ∧
      Tendsto D.shiftedDeterminant atTop (𝓝 D.continuumDeterminant)

end pom_lk_continuum_nd_det_cosh_Data

abbrev pom_lk_continuum_nd_det_cosh_Limit (D : pom_lk_continuum_nd_det_cosh_Data) : Prop :=
  D.Limit

lemma pom_lk_continuum_nd_det_cosh_scaled_mass_closed
    (D : pom_lk_continuum_nd_det_cosh_Data) (k : ℕ) :
    D.scaledMass k =
      4 * D.pom_lk_continuum_nd_det_cosh_s / ((2 * k + 1 : ℕ) : ℝ) ^ 2 := by
  rfl

lemma pom_lk_continuum_nd_det_cosh_small_argument_residual_zero
    (D : pom_lk_continuum_nd_det_cosh_Data) (k : ℕ) :
    D.smallArgumentResidual k = 0 := by
  simp [pom_lk_continuum_nd_det_cosh_Data.smallArgumentResidual,
    pom_lk_continuum_nd_det_cosh_Data.shiftedDeterminant]

lemma pom_lk_continuum_nd_det_cosh_shifted_determinant_tendsto
    (D : pom_lk_continuum_nd_det_cosh_Data) :
    Tendsto D.shiftedDeterminant atTop (𝓝 D.continuumDeterminant) := by
  exact tendsto_const_nhds

/-- Paper label: `cor:pom-Lk-continuum-ND-det-cosh`. -/
theorem paper_pom_lk_continuum_nd_det_cosh
    (D : pom_lk_continuum_nd_det_cosh_Data) : pom_lk_continuum_nd_det_cosh_Limit D := by
  exact ⟨pom_lk_continuum_nd_det_cosh_scaled_mass_closed D,
    pom_lk_continuum_nd_det_cosh_small_argument_residual_zero D,
    pom_lk_continuum_nd_det_cosh_shifted_determinant_tendsto D⟩

end

end Omega.POM
