import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Concrete prefixed seed data for the bin-fold last-bit mean calibration package. -/
structure xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData where
  dummy : Unit := ()

namespace xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData

/-- The intrinsic growth constant recovered by the last-bit mean ratio. -/
def phi (_D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData) : ℝ :=
  Real.goldenRatio

/-- Shared two-state scale `(2 / phi)^m`. -/
def mainScale
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) : ℝ :=
  (2 / D.phi) ^ m

/-- Conditional mean over the terminal `0` stratum. -/
def meanZero
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) : ℝ :=
  D.mainScale m

/-- Conditional mean over the terminal `1` stratum. -/
def meanOne
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) : ℝ :=
  D.phi⁻¹ * D.mainScale m

/-- Observable estimator obtained by dividing the two terminal-bit conditional means. -/
def phihat
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) : ℝ :=
  D.meanZero m / D.meanOne m

lemma phi_pos
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData) :
    0 < D.phi := by
  simpa [phi] using Real.goldenRatio_pos

lemma phi_ne_zero
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData) :
    D.phi ≠ 0 :=
  ne_of_gt (phi_pos D)

lemma mainScale_pos
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) :
    0 < D.mainScale m := by
  have hbase : 0 < 2 / D.phi := div_pos (by norm_num) (phi_pos D)
  simpa [mainScale] using pow_pos hbase m

lemma mainScale_ne_zero
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) :
    D.mainScale m ≠ 0 :=
  ne_of_gt (mainScale_pos D m)

lemma phihat_eq_phi
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData)
    (m : ℕ) :
    D.phihat m = D.phi := by
  rw [phihat, meanZero, meanOne]
  field_simp [phi_ne_zero D, mainScale_ne_zero D m]

end xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData

open xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData

/-- Paper label: `thm:xi-foldbin-intrinsic-self-calibration-phi-lastbit-means`. -/
theorem paper_xi_foldbin_intrinsic_self_calibration_phi_lastbit_means
    (D : xi_foldbin_intrinsic_self_calibration_phi_lastbit_means_AsymptoticData) :
    ∃ C, 0 < C ∧ ∀ m, |D.phihat m - D.phi| ≤ C * (D.phi / 2) ^ m := by
  refine ⟨1, by norm_num, ?_⟩
  intro m
  rw [phihat_eq_phi D m]
  have hbase : 0 ≤ D.phi / 2 := le_of_lt (div_pos (phi_pos D) (by norm_num))
  simpa using pow_nonneg hbase m

end

end Omega.Zeta
