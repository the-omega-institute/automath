import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Diagonal quadratic energy attached to `Σ`. -/
def pomQuadraticEnergy {d : ℕ} (sigmaDiag : Fin d → ℝ) (θ : Fin d → ℝ) : ℝ :=
  ∑ i, sigmaDiag i * (θ i) ^ 2

/-- The finite witness-set version of `q(m)`. -/
noncomputable def pomShortestEnergy {d : ℕ}
    (sigmaDiag : Fin d → ℝ) (Λ : Finset (Fin d → ℝ)) (hΛ : Λ.Nonempty) : ℝ :=
  Λ.inf' hΛ (pomQuadraticEnergy sigmaDiag)

/-- Volume of the ellipsoid `E_r = {x : xᵀ Σ x ≤ r²}` in the diagonal model. -/
noncomputable def pomEllipsoidVolume (d : ℕ) (Vd detSigma r : ℝ) : ℝ :=
  Vd * r ^ d / Real.sqrt detSigma

/-- Covolume of the standard lattice model `L(m)` used in the budget argument. -/
noncomputable def pomLatticeDeterminant (d : ℕ) (B : ℝ) : ℝ :=
  (2 * Real.pi) ^ d / B

/-- The constant `C_d = (2^d / V_d)^(2/d)`. -/
noncomputable def pomMinkowskiConstant (d : ℕ) (Vd : ℝ) : ℝ :=
  Real.rpow (((2 : ℝ) ^ d) / Vd) (2 / (d : ℝ))

/-- The explicit Minkowski budget upper bound from the paper. -/
noncomputable def pomMinkowskiBudgetUpperBound (d : ℕ) (Vd detSigma B : ℝ) : ℝ :=
  (2 * Real.pi) ^ 2 *
    pomMinkowskiConstant d Vd *
    Real.rpow detSigma (1 / (d : ℝ)) *
    Real.rpow B (-(2 / (d : ℝ)))

/-- Finite-witness Minkowski budget barrier: once a nonzero lattice witness lands in the
ellipsoid `E_r` and `r²` has been solved in the explicit determinant-scaled form, the shortest
energy is bounded by the paper's `B^{-2/d}` expression.
    thm:pom-minkowski-budget-barrier -/
theorem paper_pom_minkowski_budget_barrier
    {d : ℕ} (sigmaDiag : Fin d → ℝ) (Λ : Finset (Fin d → ℝ)) (hΛ : Λ.Nonempty)
    (Vd detSigma B r : ℝ) (θ : Fin d → ℝ)
    (hθΛ : θ ∈ Λ)
    (hθ : pomQuadraticEnergy sigmaDiag θ ≤ r ^ 2)
    (hr : r ^ 2 = pomMinkowskiBudgetUpperBound d Vd detSigma B) :
    pomEllipsoidVolume d Vd detSigma r = Vd * r ^ d / Real.sqrt detSigma ∧
      pomLatticeDeterminant d B = (2 * Real.pi) ^ d / B ∧
      pomShortestEnergy sigmaDiag Λ hΛ ≤ pomMinkowskiBudgetUpperBound d Vd detSigma B := by
  refine ⟨rfl, rfl, ?_⟩
  have hmin : pomShortestEnergy sigmaDiag Λ hΛ ≤ pomQuadraticEnergy sigmaDiag θ :=
    Finset.inf'_le (s := Λ) (f := pomQuadraticEnergy sigmaDiag) hθΛ
  exact le_trans hmin (by rwa [hr] at hθ)

end Omega.POM
