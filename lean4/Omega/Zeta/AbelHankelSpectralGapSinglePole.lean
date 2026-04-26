import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- Squared norm of the truncated pole vector `u_N = (1, |r₀|⁻¹, …, |r₀|^{-(N-1)})` written as a
recursive geometric sum. -/
def abel_hankel_spectral_gap_single_pole_poleNormSq (r0 : ℝ) : ℕ → ℝ
  | 0 => 0
  | N + 1 =>
      abel_hankel_spectral_gap_single_pole_poleNormSq r0 N + (|r0|⁻¹) ^ (2 * N)

@[simp] theorem abel_hankel_spectral_gap_single_pole_poleNormSq_zero (r0 : ℝ) :
    abel_hankel_spectral_gap_single_pole_poleNormSq r0 0 = 0 := rfl

@[simp] theorem abel_hankel_spectral_gap_single_pole_poleNormSq_succ (r0 : ℝ) (N : ℕ) :
    abel_hankel_spectral_gap_single_pole_poleNormSq r0 (N + 1) =
      abel_hankel_spectral_gap_single_pole_poleNormSq r0 N + (|r0|⁻¹) ^ (2 * N) := rfl

private lemma abel_hankel_spectral_gap_single_pole_poleNormSq_nonneg (r0 : ℝ) :
    ∀ N, 0 ≤ abel_hankel_spectral_gap_single_pole_poleNormSq r0 N
  | 0 => by simp [abel_hankel_spectral_gap_single_pole_poleNormSq]
  | N + 1 => by
      have hprev :
          0 ≤ abel_hankel_spectral_gap_single_pole_poleNormSq r0 N :=
        abel_hankel_spectral_gap_single_pole_poleNormSq_nonneg r0 N
      have hterm : 0 ≤ ((|r0| ^ (2 * N : Nat) : ℝ)⁻¹) := by
        exact inv_nonneg.mpr (pow_nonneg (abs_nonneg _) _)
      simpa [abel_hankel_spectral_gap_single_pole_poleNormSq] using add_nonneg hprev hterm

private lemma abel_hankel_spectral_gap_single_pole_last_term_le
    (c r0 : ℝ) (N : ℕ) :
    |c| * (|r0|⁻¹) ^ (2 * N) ≤
      |c| * abel_hankel_spectral_gap_single_pole_poleNormSq r0 (N + 1) := by
  simp [abel_hankel_spectral_gap_single_pole_poleNormSq]
  have htail_nonneg :
      0 ≤ |c| * abel_hankel_spectral_gap_single_pole_poleNormSq r0 N := by
    exact mul_nonneg (abs_nonneg _) (abel_hankel_spectral_gap_single_pole_poleNormSq_nonneg r0 N)
  nlinarith

/-- Concrete spectral-gap certificate for a single-pole Hankel block. The lower Weyl bound on the
leading singular value and the upper Weyl bound on the tail singular value are packaged together
with the explicit pole-vector growth coming from the geometric last term in `‖u_N‖₂²`. -/
def abel_hankel_spectral_gap_single_pole_statement : Prop :=
  ∀ {c r0 C errorOpNorm sigma1 sigma2 : ℝ} {N : ℕ},
    0 ≤ C →
    0 ≤ errorOpNorm →
    errorOpNorm ≤ (N : ℝ) * C →
    |c| * abel_hankel_spectral_gap_single_pole_poleNormSq r0 N - errorOpNorm ≤ sigma1 →
    sigma2 ≤ errorOpNorm →
    3 * (N : ℝ) * C ≤ |c| * abel_hankel_spectral_gap_single_pole_poleNormSq r0 N →
    1 ≤ N →
    |c| * (|r0|⁻¹) ^ (2 * (N - 1)) ≤ sigma1 + (N : ℝ) * C ∧
      2 * (N : ℝ) * C ≤ sigma1 ∧
      sigma2 ≤ (N : ℝ) * C

/-- Paper label: `thm:abel-hankel-spectral-gap-single-pole`. The Hankel block is controlled by a
rank-one spike of size `|c| ‖u_N‖₂²` plus an error whose operator norm is bounded by the row-sum
estimate `CN`; Weyl bounds then give the spectral gap, while the explicit geometric formula for
`‖u_N‖₂²` shows that even its last term already forces exponential growth of the leading scale. -/
theorem paper_abel_hankel_spectral_gap_single_pole :
    abel_hankel_spectral_gap_single_pole_statement := by
  intro c r0 C errorOpNorm sigma1 sigma2 N hC herror_nonneg herror_bound hsigma1 hsigma2
    hthreshold hN
  have hlead_upper :
      |c| * abel_hankel_spectral_gap_single_pole_poleNormSq r0 N ≤ sigma1 + (N : ℝ) * C := by
    linarith
  have hspectral_gap : 2 * (N : ℝ) * C ≤ sigma1 := by
    linarith
  have hsigma2_bound : sigma2 ≤ (N : ℝ) * C := le_trans hsigma2 herror_bound
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hN)
  have hgrowth :
      |c| * (|r0|⁻¹) ^ (2 * k) ≤ sigma1 + (((k + 1 : ℕ) : ℝ) * C) := by
    exact le_trans
      (abel_hankel_spectral_gap_single_pole_last_term_le c r0 k)
      hlead_upper
  exact ⟨by simpa using hgrowth, by simpa using hspectral_gap, by simpa using hsigma2_bound⟩

end

end Omega.Zeta
