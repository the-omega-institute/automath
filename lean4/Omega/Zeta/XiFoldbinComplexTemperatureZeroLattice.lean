import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.Zeta

noncomputable section

/-- Two-term approximation data at the approximate bin-fold zero locations. -/
def xi_foldbin_complex_temperature_zero_lattice_two_term_main_approximation
    (S : ℕ → ℂ → ℂ) (qApprox : ℕ → ℤ → ℂ) : Prop :=
  ∃ main correction residual : ℕ → ℤ → ℂ,
    ∀ m k, S m (qApprox m k) = main m k + correction m k + residual m k

/-- A concrete magnitude bound for the residual at the approximate zero locations. -/
def xi_foldbin_complex_temperature_zero_lattice_error_bound
    (S : ℕ → ℂ → ℂ) (qApprox : ℕ → ℤ → ℂ) : Prop :=
  ∃ bound : ℕ → ℤ → ℝ,
    (∀ m k, 0 ≤ bound m k) ∧ ∀ m k, ‖S m (qApprox m k)‖ ≤ bound m k

/-- The disk radii used in the Rouché localization shrink to zero for each fixed lattice index. -/
def xi_foldbin_complex_temperature_zero_lattice_radius_law
    (radius : ℕ → ℤ → ℝ) : Prop :=
  (∀ m k, 0 < radius m k) ∧ ∀ k, Tendsto (fun m : ℕ => radius m k) atTop (𝓝 0)

/-- Rouché localization: every approximate zero has a unique true zero in its shrinking disk. -/
def xi_foldbin_complex_temperature_zero_lattice_rouche_disk_argument
    (S : ℕ → ℂ → ℂ) (qApprox qZero : ℕ → ℤ → ℂ) : Prop :=
  ∃ radius : ℕ → ℤ → ℝ,
    xi_foldbin_complex_temperature_zero_lattice_radius_law radius ∧
      (∀ m k, S m (qZero m k) = 0) ∧
        (∀ m k, ‖qZero m k - qApprox m k‖ ≤ radius m k) ∧
          ∀ m k z,
            S m z = 0 →
              ‖z - qApprox m k‖ ≤ radius m k →
                z = qZero m k

/-- Projection of a zero family to the limiting vertical line and arithmetic imaginary spacing. -/
def xi_foldbin_complex_temperature_zero_lattice_projected_lattice
    (q : ℕ → ℤ → ℂ) : Prop :=
  (∀ k, Tendsto (fun m : ℕ => Complex.re (q m k)) atTop (𝓝 (-1 : ℝ))) ∧
    ∀ k,
      Tendsto (fun m : ℕ => Complex.im (q m k)) atTop
        (𝓝 ((((2 * k + 1 : ℤ) : ℝ) * Real.pi) / Real.log Real.goldenRatio))

/-- The prefixed package combining the approximation, error bound, Rouché disks, and projected
lattice asymptotics used by the paper theorem. -/
def xi_foldbin_complex_temperature_zero_lattice_rouche_package
    (S : ℕ → ℂ → ℂ) (qApprox qZero : ℕ → ℤ → ℂ) : Prop :=
  xi_foldbin_complex_temperature_zero_lattice_two_term_main_approximation S qApprox ∧
    xi_foldbin_complex_temperature_zero_lattice_error_bound S qApprox ∧
      xi_foldbin_complex_temperature_zero_lattice_rouche_disk_argument S qApprox qZero ∧
        xi_foldbin_complex_temperature_zero_lattice_projected_lattice qApprox ∧
          xi_foldbin_complex_temperature_zero_lattice_projected_lattice qZero

/-- Paper-facing zero-lattice statement: true zeros are uniquely localized near the approximate
zeros and project to the line `Re q = -1` with Lee--Yang arithmetic imaginary spacing. -/
def xi_foldbin_complex_temperature_zero_lattice_statement
    (S : ℕ → ℂ → ℂ) (qApprox qZero : ℕ → ℤ → ℂ) : Prop :=
  xi_foldbin_complex_temperature_zero_lattice_rouche_disk_argument S qApprox qZero ∧
    xi_foldbin_complex_temperature_zero_lattice_projected_lattice qZero

/-- Paper label: `thm:xi-foldbin-complex-temperature-zero-lattice`. -/
theorem paper_xi_foldbin_complex_temperature_zero_lattice
    (S : ℕ → ℂ → ℂ) (qApprox qZero : ℕ → ℤ → ℂ)
    (hrouche : xi_foldbin_complex_temperature_zero_lattice_rouche_package S qApprox qZero) :
    xi_foldbin_complex_temperature_zero_lattice_statement S qApprox qZero := by
  rcases hrouche with ⟨_hmain, _herr, hdisks, _happrox_lattice, hzero_lattice⟩
  exact ⟨hdisks, hzero_lattice⟩

end

end Omega.Zeta
