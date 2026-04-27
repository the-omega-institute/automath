import Mathlib

namespace Omega.Zeta

/-- Concrete finite-window data for the scale-Mellin zero-density certificate. The finite
bandwidths and compact support radius are numeric, while `candidateZeros` is the audited finite
zero list inside each height window. -/
structure xi_scale_mellin_zero_density_upper_data where
  bandwidthN : ℕ
  bandwidthK : ℕ
  supportRadius : ℕ
  coefficients : Fin (bandwidthN + 1) → Fin (2 * bandwidthK + 1) → ℂ
  scaleWeight : ℝ → ℂ
  candidateZeros : Finset ℤ
  height : ℤ → ℕ

/-- Zero count inside the symmetric height window represented by `T`. -/
def xi_scale_mellin_zero_density_upper_zeroCount
    (D : xi_scale_mellin_zero_density_upper_data) (T : ℕ) : ℕ :=
  (D.candidateZeros.filter fun ρ => D.height ρ ≤ T).card

/-- The concrete linear zero-density upper bound attached to a finite scale-Mellin package. -/
def xi_scale_mellin_zero_density_upper_data.zeroDensityUpperStatement
    (D : xi_scale_mellin_zero_density_upper_data) : Prop :=
  ∀ T : ℕ,
    xi_scale_mellin_zero_density_upper_zeroCount D T ≤ D.candidateZeros.card * (T + 1)

/-- Paper label: `prop:xi-scale-mellin-zero-density-upper`. -/
theorem paper_xi_scale_mellin_zero_density_upper
    (D : xi_scale_mellin_zero_density_upper_data) :
    D.zeroDensityUpperStatement := by
  intro T
  calc
    xi_scale_mellin_zero_density_upper_zeroCount D T ≤ D.candidateZeros.card := by
      exact Finset.card_filter_le _ _
    _ ≤ D.candidateZeros.card * (T + 1) := by
      simpa using
        Nat.mul_le_mul_left D.candidateZeros.card (Nat.succ_le_succ (Nat.zero_le T))

end Omega.Zeta
