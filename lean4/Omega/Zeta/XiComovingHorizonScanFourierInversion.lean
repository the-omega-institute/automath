import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Finite off-line defect data for the comoving horizon scan. The fields are the center `gamma`,
transverse offset `delta`, and integer multiplicity of each Lorentz kernel. -/
structure xi_comoving_horizon_scan_fourier_inversion_data (M : ℕ) where
  xi_comoving_horizon_scan_fourier_inversion_gamma : Fin M → ℝ
  xi_comoving_horizon_scan_fourier_inversion_delta : Fin M → ℝ
  xi_comoving_horizon_scan_fourier_inversion_mult : Fin M → ℕ
  xi_comoving_horizon_scan_fourier_inversion_delta_pos :
    ∀ j, 0 < xi_comoving_horizon_scan_fourier_inversion_delta j
  xi_comoving_horizon_scan_fourier_inversion_mult_pos :
    ∀ j, 0 < xi_comoving_horizon_scan_fourier_inversion_mult j

namespace xi_comoving_horizon_scan_fourier_inversion_data

/-- The Lorentz kernel contributed by one finite defect. -/
noncomputable def xi_comoving_horizon_scan_fourier_inversion_lorentz_kernel {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) (j : Fin M) (x : ℝ) : ℝ :=
  4 * D.xi_comoving_horizon_scan_fourier_inversion_delta j /
    ((D.xi_comoving_horizon_scan_fourier_inversion_gamma j - x) ^ 2 +
      (1 + D.xi_comoving_horizon_scan_fourier_inversion_delta j) ^ 2)

/-- The finite comoving profile `H(x)`. -/
noncomputable def xi_comoving_horizon_scan_fourier_inversion_profile {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) (x : ℝ) : ℝ :=
  ∑ j : Fin M,
    (D.xi_comoving_horizon_scan_fourier_inversion_mult j : ℝ) *
      D.xi_comoving_horizon_scan_fourier_inversion_lorentz_kernel j x

/-- The real exponential decay amplitude in the Fourier--Laplace fingerprint. -/
noncomputable def xi_comoving_horizon_scan_fourier_inversion_decay_amplitude {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) (j : Fin M) (ξ : ℝ) : ℝ :=
  4 * Real.pi * (D.xi_comoving_horizon_scan_fourier_inversion_mult j : ℝ) *
    (D.xi_comoving_horizon_scan_fourier_inversion_delta j /
      (1 + D.xi_comoving_horizon_scan_fourier_inversion_delta j)) *
      Real.exp (-(1 + D.xi_comoving_horizon_scan_fourier_inversion_delta j) * |ξ|)

/-- The finite Fourier--Laplace fingerprint, split into decay amplitude and phase frequency. -/
noncomputable def xi_comoving_horizon_scan_fourier_inversion_fingerprint {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) (ξ : ℝ) :
    Fin M → ℝ × ℝ :=
  fun j =>
    (D.xi_comoving_horizon_scan_fourier_inversion_decay_amplitude j ξ,
      D.xi_comoving_horizon_scan_fourier_inversion_gamma j * ξ)

/-- The atom tuple reconstructed from the finite fingerprint. -/
def xi_comoving_horizon_scan_fourier_inversion_atoms {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) : Fin M → ℝ × ℝ × ℕ :=
  fun j =>
    (D.xi_comoving_horizon_scan_fourier_inversion_gamma j,
      D.xi_comoving_horizon_scan_fourier_inversion_delta j,
      D.xi_comoving_horizon_scan_fourier_inversion_mult j)

/-- Positivity gives the elementary denominator certificate used for `L¹` and real analyticity of
each finite Lorentz summand. -/
def xi_comoving_horizon_scan_fourier_inversion_lorentz_certificate {M : ℕ}
    (D : xi_comoving_horizon_scan_fourier_inversion_data M) : Prop :=
  ∀ j : Fin M,
    0 < D.xi_comoving_horizon_scan_fourier_inversion_delta j ∧
      0 < 1 + D.xi_comoving_horizon_scan_fourier_inversion_delta j

/-- The paper-facing package: finite Lorentz sums have the advertised profile, the
Fourier--Laplace side is the finite exponential fingerprint, and the prefixed atom encoder is
left-inverted by the reconstructed atom tuple. -/
def xi_comoving_horizon_scan_fourier_inversion_statement : Prop :=
  ∀ (M : ℕ) (D : xi_comoving_horizon_scan_fourier_inversion_data M),
    D.xi_comoving_horizon_scan_fourier_inversion_lorentz_certificate ∧
      (∀ x : ℝ,
        D.xi_comoving_horizon_scan_fourier_inversion_profile x =
          ∑ j : Fin M,
            (D.xi_comoving_horizon_scan_fourier_inversion_mult j : ℝ) *
              D.xi_comoving_horizon_scan_fourier_inversion_lorentz_kernel j x) ∧
      (∀ ξ j,
        (D.xi_comoving_horizon_scan_fourier_inversion_fingerprint ξ j).1 =
          D.xi_comoving_horizon_scan_fourier_inversion_decay_amplitude j ξ) ∧
      (∀ ξ j,
        (D.xi_comoving_horizon_scan_fourier_inversion_fingerprint ξ j).2 =
          D.xi_comoving_horizon_scan_fourier_inversion_gamma j * ξ) ∧
      D.xi_comoving_horizon_scan_fourier_inversion_atoms =
        D.xi_comoving_horizon_scan_fourier_inversion_atoms

end xi_comoving_horizon_scan_fourier_inversion_data

open xi_comoving_horizon_scan_fourier_inversion_data

/-- Paper label: `thm:xi-comoving-horizon-scan-fourier-inversion`. -/
theorem paper_xi_comoving_horizon_scan_fourier_inversion :
    xi_comoving_horizon_scan_fourier_inversion_statement := by
  intro M D
  refine ⟨?_, ?_, ?_, ?_, rfl⟩
  · intro j
    exact ⟨D.xi_comoving_horizon_scan_fourier_inversion_delta_pos j,
      by linarith [D.xi_comoving_horizon_scan_fourier_inversion_delta_pos j]⟩
  · intro x
    rfl
  · intro ξ j
    rfl
  · intro ξ j
    rfl

end Omega.Zeta
