import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Complex.Basic
import Omega.GU.JoukowskyGodelLeadingCoeffRigidity

namespace Omega.GU

open scoped BigOperators

/-- The Lee-Yang/Mahler free-energy contribution obtained from the transport leading coefficient
and the radial scale `r`. -/
noncomputable def leyangMahlerFreeEnergy
    (n : ℕ) (r : ℝ) (a_n : ℂ) (_a_0 : ℂ) (roots : Fin n → ℂ) : ℝ :=
  Real.log ‖a_n ^ 2 * (((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖ + n * Real.log r

private lemma leeYang_root_product_norm_one (n : ℕ) (roots : Fin n → ℂ)
    (hLeeYang : ∀ j, ‖roots j‖ = 1) :
    ‖(((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖ = 1 := by
  calc
    ‖(((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖
        = ‖(-1 : ℂ) ^ n‖ * ‖∏ j : Fin n, roots j‖ := by rw [norm_mul]
    _ = 1 * ‖∏ j : Fin n, roots j‖ := by simp
    _ = 1 * ∏ j : Fin n, ‖roots j‖ := by rw [norm_prod]
    _ = 1 := by simp [hLeeYang]

set_option maxHeartbeats 400000 in
/-- Under the Lee-Yang unit-circle root condition, the transport free energy collapses to the
Mahler term `log |a_n a_0| + n log r`; equivalently `|a_0| = |a_n|`.
    thm:group-jg-leyang-mahler-free-energy -/
theorem paper_group_jg_leyang_mahler_free_energy
    (n : ℕ) (r : ℝ) (a_n a_0 : ℂ) (roots : Fin n → ℂ) (_hr : 0 < r)
    (hVieta : a_n * (((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j) = a_0)
    (hLeeYang : ∀ j, ‖roots j‖ = 1) :
    leyangMahlerFreeEnergy n r a_n a_0 roots = Real.log ‖a_n * a_0‖ + n * Real.log r ∧
      ‖a_0‖ = ‖a_n‖ := by
  let D : JoukowskyGodelTransportData ℂ :=
    { n := n, a_n := a_n, a_0 := a_0, r := (r : ℂ), roots := roots, hVieta := hVieta }
  have hrigid : D.leadingCoeffRigidity := paper_group_jg_lc_rigidity D
  have hcircle : ‖(((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖ = 1 :=
    leeYang_root_product_norm_one n roots hLeeYang
  have hnorm : ‖a_0‖ = ‖a_n‖ := by
    calc
      ‖a_0‖ = ‖a_n * (((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖ := by rw [← hVieta]
      _ = ‖a_n‖ * ‖(((-1 : ℂ) ^ n) * ∏ j : Fin n, roots j)‖ := by rw [norm_mul]
      _ = ‖a_n‖ := by rw [hcircle]; ring
  refine ⟨?_, hnorm⟩
  unfold leyangMahlerFreeEnergy
  dsimp [JoukowskyGodelTransportData.leadingCoeffRigidity,
    JoukowskyGodelTransportData.transportLeadingCoeff] at hrigid
  rw [hrigid]

/-- An affine free-energy profile has constant logarithmic flux equal to its linear coefficient.
    cor:group-jg-leyang-free-energy-linear-flux -/
theorem paper_group_jg_leyang_free_energy_linear_flux (n : ℕ) (c t : ℝ) :
    HasDerivAt (fun s : ℝ => c + n * s) n t := by
  simpa [mul_comm, mul_left_comm, mul_assoc] using
    (((hasDerivAt_id t).const_mul (n : ℝ)).const_add c)

end Omega.GU
