import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The explicit bulk correction coming from the logarithmic boundary offsets. -/
noncomputable def xiBulkLogGap (κ : ℕ) (δ : Fin κ → ℝ) : ℝ :=
  ∑ j : Fin κ, Real.log ((1 + δ j) / δ j)

/-- Scalar model for the logarithm of the bulk Jacobian factor. -/
noncomputable def xiBulkJacobianLog (κ : ℕ) (δ : Fin κ → ℝ) (m : ℝ) : ℝ :=
  -((κ : ℝ) ^ 2) * Real.log m + ((2 : ℝ) * κ - 1) * xiBulkLogGap κ δ

/-- Concrete bulk entropy profile with the Jacobian factor pulled out at `m = 1`. -/
noncomputable def xiBulkEntropyModel (κ : ℕ) (δ : Fin κ → ℝ) (Sbulk₁ m : ℝ) : ℝ :=
  Sbulk₁ - xiBulkJacobianLog κ δ m

/-- Boundary entropy obeying the linear logarithmic law from the paper argument. -/
noncomputable def xiGenEntropyModel (κ : ℕ) (Sgen₁ m : ℝ) : ℝ :=
  Sgen₁ + (κ : ℝ) * Real.log m

/-- Renormalized constant term obtained after removing the `κ² log m` bulk divergence. -/
noncomputable def xiBulkRenormalizedConstant (κ : ℕ) (δ : Fin κ → ℝ) (Sbulk₁ : ℝ) : ℝ :=
  Sbulk₁ - ((2 : ℝ) * κ - 1) * xiBulkLogGap κ δ

/-- Limiting bulk-boundary anomaly gap after subtracting `κ S_gen(m)`. -/
noncomputable def xiBulkAnomalyGap (κ : ℕ) (δ : Fin κ → ℝ) (Sbulk₁ Sgen₁ : ℝ) : ℝ :=
  xiBulkRenormalizedConstant κ δ Sbulk₁ - (κ : ℝ) * Sgen₁

/-- Paper label: `thm:xi-bulk-renormalized-constant-and-anomaly-gap`.

In the concrete scalar model, subtracting the `κ² log m` divergence leaves the closed bulk
constant, and subtracting `κ S_gen(m)` leaves the closed anomaly gap. -/
theorem paper_xi_bulk_renormalized_constant_and_anomaly_gap
    (κ : ℕ) (δ : Fin κ → ℝ) (Sbulk₁ Sgen₁ m : ℝ) :
    xiBulkEntropyModel κ δ Sbulk₁ m - (κ : ℝ) ^ 2 * Real.log m =
      xiBulkRenormalizedConstant κ δ Sbulk₁ ∧
      xiBulkEntropyModel κ δ Sbulk₁ m - (κ : ℝ) * xiGenEntropyModel κ Sgen₁ m =
        xiBulkAnomalyGap κ δ Sbulk₁ Sgen₁ := by
  constructor
  · unfold xiBulkEntropyModel xiBulkJacobianLog xiBulkRenormalizedConstant
    ring
  · unfold xiBulkEntropyModel xiBulkJacobianLog xiGenEntropyModel xiBulkAnomalyGap
    unfold xiBulkRenormalizedConstant
    ring

end Omega.Zeta
