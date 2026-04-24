import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic
import Omega.POM.LkChebyshevCharpoly

namespace Omega.POM

noncomputable section

/-- The positive square-root parameter `x = sqrt (1 + t / 4)` used in the shifted `L_k`
determinant discussion. -/
def pom_lk_shifted_det_free_energy_root (t : ℝ) : ℝ :=
  Real.sqrt (1 + t / 4)

/-- The bulk free-energy density extracted from the positive branch of `x`. -/
def pom_lk_shifted_det_free_energy_density (t : ℝ) : ℝ :=
  2 * Real.log (pom_lk_shifted_det_free_energy_root t)

/-- The renormalized constant term attached to the same branch. -/
def pom_lk_shifted_det_free_energy_constant (t : ℝ) : ℝ :=
  -Real.log (pom_lk_shifted_det_free_energy_root t)

/-- Concrete statement for the shifted `L_k` determinant/free-energy package. It records the
existing Chebyshev closed form together with the positive square-root substitution and the affine
decomposition of the logarithm into a bulk term plus a renormalized constant. -/
def pom_lk_shifted_det_free_energy_statement (k : ℕ) (t : ℝ) : Prop :=
  let D : LkChebyshevCharpolyData := ⟨k⟩
  D.charpolyClosedForm ∧
    0 < pom_lk_shifted_det_free_energy_root t ∧
    pom_lk_shifted_det_free_energy_root t ^ 2 = 1 + t / 4 ∧
    pom_lk_shifted_det_free_energy_density t =
      2 * Real.log (pom_lk_shifted_det_free_energy_root t) ∧
    pom_lk_shifted_det_free_energy_constant t =
      -Real.log (pom_lk_shifted_det_free_energy_root t) ∧
    (k : ℝ) * pom_lk_shifted_det_free_energy_density t +
        pom_lk_shifted_det_free_energy_constant t =
      (2 * (k : ℝ) - 1) * Real.log (pom_lk_shifted_det_free_energy_root t)

/-- Paper label: `cor:pom-Lk-shifted-det-free-energy`. -/
theorem paper_pom_lk_shifted_det_free_energy (k : ℕ) (t : ℝ) (ht : -4 < t) :
    pom_lk_shifted_det_free_energy_statement k t := by
  let D : LkChebyshevCharpolyData := ⟨k⟩
  have hchar : D.charpolyClosedForm := by
    exact (paper_pom_lk_chebyshev_charpoly D).2.1
  have hposArg : 0 < 1 + t / 4 := by
    nlinarith
  have hnonnegArg : 0 ≤ 1 + t / 4 := by
    linarith
  have hroot_pos : 0 < pom_lk_shifted_det_free_energy_root t := by
    exact Real.sqrt_pos.mpr hposArg
  have hroot_sq :
      pom_lk_shifted_det_free_energy_root t ^ 2 = 1 + t / 4 := by
    dsimp [pom_lk_shifted_det_free_energy_root]
    nlinarith [Real.sq_sqrt hnonnegArg]
  refine ⟨hchar, hroot_pos, hroot_sq, rfl, rfl, ?_⟩
  unfold pom_lk_shifted_det_free_energy_density pom_lk_shifted_det_free_energy_constant
  ring_nf

end

end Omega.POM
