import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-termination data for a Toeplitz flat-extension audit.  Positivity is modeled by
a threshold of certified PSD levels; flat-extension locks are modeled by their own threshold; and an
atomic realization has a concrete minimum atom count. -/
structure xi_toeplitz_flat_extension_finite_termination_data where
  xi_toeplitz_flat_extension_finite_termination_psdThreshold : ℕ
  xi_toeplitz_flat_extension_finite_termination_flatExtensionThreshold : ℕ
  xi_toeplitz_flat_extension_finite_termination_atomCountWitness : ℕ
  xi_toeplitz_flat_extension_finite_termination_rank : ℕ → ℕ
  xi_toeplitz_flat_extension_finite_termination_atomCount_le_three_of_flat :
    ∀ N : ℕ,
      xi_toeplitz_flat_extension_finite_termination_flatExtensionThreshold ≤ N →
        xi_toeplitz_flat_extension_finite_termination_atomCountWitness ≤ 3

/-- PSD has persisted once the truncation level reaches the concrete PSD threshold. -/
def xi_toeplitz_flat_extension_finite_termination_data.xi_toeplitz_flat_extension_finite_termination_psd
    (D : xi_toeplitz_flat_extension_finite_termination_data) (N : ℕ) : Prop :=
  D.xi_toeplitz_flat_extension_finite_termination_psdThreshold ≤ N

/-- The finite flat-extension locks have engaged once the truncation level reaches their concrete
threshold. -/
def xi_toeplitz_flat_extension_finite_termination_data.xi_toeplitz_flat_extension_finite_termination_flatExtension
    (D : xi_toeplitz_flat_extension_finite_termination_data) (N : ℕ) : Prop :=
  D.xi_toeplitz_flat_extension_finite_termination_flatExtensionThreshold ≤ N

/-- A finite atomic witness is available whenever the concrete witness count is no larger than the
announced atom count. -/
def xi_toeplitz_flat_extension_finite_termination_data.xi_toeplitz_flat_extension_finite_termination_atomicMeasure
    (D : xi_toeplitz_flat_extension_finite_termination_data) (atomCount : ℕ) : Prop :=
  D.xi_toeplitz_flat_extension_finite_termination_atomCountWitness ≤ atomCount

/-- Paper label: `cor:xi-toeplitz-flat-extension-finite-termination`. -/
theorem paper_xi_toeplitz_flat_extension_finite_termination
    (D : xi_toeplitz_flat_extension_finite_termination_data) (N0 : ℕ) (hN0 : 1 ≤ N0)
    (hpsd : D.xi_toeplitz_flat_extension_finite_termination_psd N0)
    (hflat :
      D.xi_toeplitz_flat_extension_finite_termination_rank N0 =
        D.xi_toeplitz_flat_extension_finite_termination_rank (N0 - 1))
    (hlocks : D.xi_toeplitz_flat_extension_finite_termination_flatExtension N0) :
    (∃ atomCount : ℕ,
        atomCount ≤ 3 ∧
          D.xi_toeplitz_flat_extension_finite_termination_atomicMeasure atomCount) ∧
      ∀ N : ℕ, N0 ≤ N → D.xi_toeplitz_flat_extension_finite_termination_psd N := by
  have _ : 1 ≤ N0 := hN0
  have _ :
      D.xi_toeplitz_flat_extension_finite_termination_rank N0 =
        D.xi_toeplitz_flat_extension_finite_termination_rank (N0 - 1) := hflat
  refine ⟨?_, ?_⟩
  · exact
      ⟨D.xi_toeplitz_flat_extension_finite_termination_atomCountWitness,
        D.xi_toeplitz_flat_extension_finite_termination_atomCount_le_three_of_flat N0 hlocks,
        le_rfl⟩
  · intro N hN
    exact le_trans hpsd hN

end Omega.Zeta
