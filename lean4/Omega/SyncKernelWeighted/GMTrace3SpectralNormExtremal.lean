import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Jensen's lower envelope for the third trace moment after fixing the top eigenvalue. -/
noncomputable def gmTrace3LowerEnvelope (m : ℕ) (S1 x : ℝ) : ℝ :=
  x ^ 3 + (S1 - x) ^ 3 / ((m - 1 : ℝ) ^ 2)

/-- The cubic obtained by clearing denominators in `gmTrace3LowerEnvelope m S1 x = S3`. -/
noncomputable def gmTrace3Cubic (m : ℕ) (S1 S3 x : ℝ) : ℝ :=
  (m : ℝ) * ((m : ℝ) - 2) * x ^ 3 + 3 * S1 * x ^ 2 - 3 * S1 ^ 2 * x +
    (S1 ^ 3 - ((m - 1 : ℝ) ^ 2) * S3)

private lemma gmTrace3LowerEnvelope_shifted
    (m : ℕ) (hm : 2 ≤ m) (S1 z : ℝ) :
    gmTrace3LowerEnvelope m S1 (S1 / (m : ℝ) + z) =
      S1 ^ 3 / (m : ℝ) ^ 2 +
        (3 * S1 / (m - 1 : ℝ)) * z ^ 2 +
        (((m : ℝ) * ((m : ℝ) - 2)) / ((m - 1 : ℝ) ^ 2)) * z ^ 3 := by
  have hm0 : (m : ℝ) ≠ 0 := by
    exact_mod_cast (show m ≠ 0 by omega)
  have hm1 : (m - 1 : ℝ) ≠ 0 := by
    have hm1' : 1 < (m : ℝ) := by
      exact_mod_cast hm
    linarith
  unfold gmTrace3LowerEnvelope
  field_simp [hm0, hm1]
  ring

private lemma gmTrace3LowerEnvelope_eq_iff_cubic_eq_zero
    (m : ℕ) (hm : 2 ≤ m) (S1 S3 x : ℝ) :
    gmTrace3LowerEnvelope m S1 x = S3 ↔ gmTrace3Cubic m S1 S3 x = 0 := by
  have hm1 : (m - 1 : ℝ) ≠ 0 := by
    have hm1' : 1 < (m : ℝ) := by
      exact_mod_cast hm
    linarith
  constructor <;> intro h
  · rw [gmTrace3LowerEnvelope] at h
    unfold gmTrace3Cubic
    field_simp [hm1] at h ⊢
    nlinarith
  · unfold gmTrace3Cubic at h
    rw [gmTrace3LowerEnvelope]
    field_simp [hm1] at h ⊢
    nlinarith

/-- Paper label: `thm:gm-trace3-spectral-norm-extremal`.
Fixing the top eigenvalue produces the Jensen lower envelope
`x ↦ x^3 + (S1 - x)^3 / (m - 1)^2`. After recentering at `S1 / m`, this envelope becomes a
constant plus a polynomial with nonnegative coefficients, hence is monotone for nonnegative
displacements; clearing denominators gives the paper's cubic, and the two-point spectrum is read
off from `y = (S1 - x) / (m - 1)`. -/
theorem paper_gm_trace3_spectral_norm_extremal
    (m : ℕ) (hm : 2 ≤ m) {S1 S3 u v : ℝ}
    (hS1 : 0 ≤ S1) (hu : 0 ≤ u) (huv : u ≤ v) :
    let x := S1 / (m : ℝ) + u
    let x' := S1 / (m : ℝ) + v
    let y := (S1 - x) / (m - 1 : ℝ)
    gmTrace3LowerEnvelope m S1 x ≤ gmTrace3LowerEnvelope m S1 x' ∧
      (gmTrace3LowerEnvelope m S1 x = S3 ↔ gmTrace3Cubic m S1 S3 x = 0) ∧
      x + (m - 1 : ℝ) * y = S1 ∧
      x ^ 3 + (m - 1 : ℝ) * y ^ 3 = gmTrace3LowerEnvelope m S1 x := by
  dsimp
  have hu2v2 : u ^ 2 ≤ v ^ 2 := by nlinarith
  have hu3v3 : u ^ 3 ≤ v ^ 3 := by nlinarith
  have hcoeff2 : 0 ≤ 3 * S1 / (m - 1 : ℝ) := by
    have hm1 : 0 < (m - 1 : ℝ) := by
      have hm1' : 1 < (m : ℝ) := by
        exact_mod_cast hm
      linarith
    positivity
  have hcoeff3 : 0 ≤ ((m : ℝ) * ((m : ℝ) - 2)) / ((m - 1 : ℝ) ^ 2) := by
    have hm2 : 2 ≤ (m : ℝ) := by
      exact_mod_cast hm
    have hm2' : 0 ≤ (m : ℝ) - 2 := by nlinarith
    positivity
  have hmono :
      gmTrace3LowerEnvelope m S1 (S1 / (m : ℝ) + u) ≤
        gmTrace3LowerEnvelope m S1 (S1 / (m : ℝ) + v) := by
    rw [gmTrace3LowerEnvelope_shifted m hm S1 u, gmTrace3LowerEnvelope_shifted m hm S1 v]
    nlinarith
  have hcubic :
      gmTrace3LowerEnvelope m S1 (S1 / (m : ℝ) + u) = S3 ↔
        gmTrace3Cubic m S1 S3 (S1 / (m : ℝ) + u) = 0 :=
    gmTrace3LowerEnvelope_eq_iff_cubic_eq_zero m hm S1 S3 (S1 / (m : ℝ) + u)
  have hm1 : (m - 1 : ℝ) ≠ 0 := by
    have hm1' : 1 < (m : ℝ) := by
      exact_mod_cast hm
    linarith
  have hy_sum :
      (S1 / (m : ℝ) + u) +
          (m - 1 : ℝ) * ((S1 - (S1 / (m : ℝ) + u)) / (m - 1 : ℝ)) =
        S1 := by
    field_simp [hm1]
    ring
  have hy_cube :
      (S1 / (m : ℝ) + u) ^ 3 +
          (m - 1 : ℝ) * ((S1 - (S1 / (m : ℝ) + u)) / (m - 1 : ℝ)) ^ 3 =
        gmTrace3LowerEnvelope m S1 (S1 / (m : ℝ) + u) := by
    unfold gmTrace3LowerEnvelope
    field_simp [hm1]
  exact ⟨hmono, hcubic, hy_sum, hy_cube⟩

end Omega.SyncKernelWeighted
