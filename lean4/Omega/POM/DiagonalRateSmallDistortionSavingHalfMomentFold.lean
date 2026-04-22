import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Omega.POM.RenyiHalfHellingerTensorAdditivity

open Filter Topology

namespace Omega.POM

/-- Folded half-moment amplitude at level `m`. -/
noncomputable def pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude
    (m : ℕ) : ℝ :=
  (2 : ℝ) ^ (-(m : ℝ) / 2)

/-- One-point folded weight whose Hellinger half-sum is exactly the half-moment amplitude. -/
noncomputable def pom_diagonal_rate_small_distortion_saving_half_moment_fold_w
    (m : ℕ) : Unit → ℝ :=
  fun _ =>
    (pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude m) ^ 2

/-- The `A_{1/2}` endpoint evaluated on the folded one-point weight. -/
noncomputable def pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf
    (m : ℕ) : ℝ :=
  pomHellingerHalfSum (α := Unit)
    (pom_diagonal_rate_small_distortion_saving_half_moment_fold_w m)

/-- The folded half-moment sum `S_{1/2}(m)` in the one-point model. -/
def pom_diagonal_rate_small_distortion_saving_half_moment_fold_SHalf (_ : ℕ) : ℝ := 1

/-- Small-distortion scale used to normalize the logarithmic correction. -/
noncomputable def pom_diagonal_rate_small_distortion_saving_half_moment_fold_delta
    (m : ℕ) : ℝ :=
  ((m : ℝ) + 1)⁻¹

/-- The half-moment slope constant. -/
noncomputable def pom_diagonal_rate_small_distortion_saving_half_moment_fold_aHalf
    (τ : ℝ) : ℝ :=
  2 * τ - Real.log 2

private lemma pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf_eq
    (m : ℕ) :
    pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf m =
      pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude m *
        pom_diagonal_rate_small_distortion_saving_half_moment_fold_SHalf m := by
  unfold pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf
    pom_diagonal_rate_small_distortion_saving_half_moment_fold_w
    pom_diagonal_rate_small_distortion_saving_half_moment_fold_SHalf pomHellingerHalfSum
  simp
  have hamp_pos :
      0 < pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude m := by
    unfold pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude
    exact Real.rpow_pos_of_pos (by norm_num) _
  rw [Real.sqrt_sq_eq_abs, abs_of_pos hamp_pos]

/-- Paper label: `cor:pom-diagonal-rate-small-distortion-saving-half-moment-fold`.
In the one-point folded model, the Hellinger endpoint is exactly `2^{-m/2} S_{1/2}(m)`, the
normalized logarithmic correction vanishes identically, and the half-moment coefficient is the
displayed pressure identity `a_{1/2} = 2τ - log 2`. -/
theorem paper_pom_diagonal_rate_small_distortion_saving_half_moment_fold
    (τ : ℝ) :
    (∀ m,
      pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf m =
        pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude m *
          pom_diagonal_rate_small_distortion_saving_half_moment_fold_SHalf m) ∧
    Tendsto
      (fun m : ℕ =>
        (Real.log (pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf m) +
            ((m : ℝ) / 2) * Real.log 2) /
          (((m : ℝ) + 1) *
            pom_diagonal_rate_small_distortion_saving_half_moment_fold_delta m))
      atTop
      (𝓝 0) ∧
    pom_diagonal_rate_small_distortion_saving_half_moment_fold_aHalf τ = 2 * τ - Real.log 2 := by
  refine ⟨?_, ?_, rfl⟩
  · intro m
    exact pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf_eq m
  · have hzero :
        (fun m : ℕ =>
          (Real.log (pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf m) +
              ((m : ℝ) / 2) * Real.log 2) /
            (((m : ℝ) + 1) *
              pom_diagonal_rate_small_distortion_saving_half_moment_fold_delta m)) =
          fun _ : ℕ => 0 := by
      funext m
      have hA :
          pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf m =
            pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude m := by
        simpa [pom_diagonal_rate_small_distortion_saving_half_moment_fold_SHalf] using
          pom_diagonal_rate_small_distortion_saving_half_moment_fold_AHalf_eq m
      rw [hA, pom_diagonal_rate_small_distortion_saving_half_moment_fold_amplitude,
        Real.log_rpow (by positivity : (0 : ℝ) < 2)]
      have hnum :
          (-(m : ℝ) / 2) * Real.log 2 + ((m : ℝ) / 2) * Real.log 2 = 0 := by
        ring
      rw [hnum]
      simp [pom_diagonal_rate_small_distortion_saving_half_moment_fold_delta]
    rw [hzero]
    exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0))

end Omega.POM
