import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The real Möbius transform used by the basepoint scan covariance seed. -/
def xi_basepoint_scan_psl2r_covariance_mobius (a b c d x : ℝ) : ℝ :=
  (a * x + b) / (c * x + d)

/-- The determinant of the real projective matrix. -/
def xi_basepoint_scan_psl2r_covariance_delta (a b c d : ℝ) : ℝ :=
  a * d - b * c

/-- One Cauchy scan channel, written as a rank-one kernel. -/
def xi_basepoint_scan_psl2r_covariance_cauchy_kernel (p x y : ℝ) : ℝ :=
  (1 / (x - p)) * (1 / (y - p))

/-- One transformed Cauchy scan channel, including the PSL(2,R) weight factor. -/
def xi_basepoint_scan_psl2r_covariance_transformed_channel
    (a b c d p x : ℝ) : ℝ :=
  xi_basepoint_scan_psl2r_covariance_delta a b c d / (c * p + d) *
    (1 /
      (xi_basepoint_scan_psl2r_covariance_mobius a b c d x -
        xi_basepoint_scan_psl2r_covariance_mobius a b c d p))

/-- The transformed Cauchy channel with the usual PSL(2,R) weight renormalization. -/
def xi_basepoint_scan_psl2r_covariance_transformed_kernel
    (a b c d p x y : ℝ) : ℝ :=
  xi_basepoint_scan_psl2r_covariance_transformed_channel a b c d p x *
    xi_basepoint_scan_psl2r_covariance_transformed_channel a b c d p y

/-- The determinant of a two-point Gram block. -/
def xi_basepoint_scan_psl2r_covariance_gram2_det
    (K00 K01 K10 K11 : ℝ) : ℝ :=
  K00 * K11 - K01 * K10

/-- The same two-point Gram determinant after diagonal scan scaling. -/
def xi_basepoint_scan_psl2r_covariance_scaled_gram2_det
    (K00 K01 K10 K11 sx sy : ℝ) : ℝ :=
  xi_basepoint_scan_psl2r_covariance_gram2_det
    (sx * sx * K00) (sx * sy * K01) (sy * sx * K10) (sy * sy * K11)

/-- Squared normalized correlation of a two-point Gram block. -/
def xi_basepoint_scan_psl2r_covariance_normalized_correlation
    (Kxx Kxy Kyy : ℝ) : ℝ :=
  Kxy ^ 2 / (Kxx * Kyy)

/-- Concrete statement package for PSL(2,R) covariance of the scan kernel and its invariants. -/
def xi_basepoint_scan_psl2r_covariance_statement : Prop :=
  (∀ a b c d p x y : ℝ,
    xi_basepoint_scan_psl2r_covariance_delta a b c d ≠ 0 →
      c * p + d ≠ 0 →
        c * x + d ≠ 0 →
          c * y + d ≠ 0 →
            x - p ≠ 0 →
              y - p ≠ 0 →
                xi_basepoint_scan_psl2r_covariance_mobius a b c d x -
                    xi_basepoint_scan_psl2r_covariance_mobius a b c d p ≠ 0 →
                  xi_basepoint_scan_psl2r_covariance_mobius a b c d y -
                      xi_basepoint_scan_psl2r_covariance_mobius a b c d p ≠ 0 →
                    xi_basepoint_scan_psl2r_covariance_transformed_kernel a b c d p x y =
                      (c * x + d) * (c * y + d) *
                        xi_basepoint_scan_psl2r_covariance_cauchy_kernel p x y) ∧
    (∀ K00 K01 K10 K11 sx sy : ℝ,
      xi_basepoint_scan_psl2r_covariance_scaled_gram2_det K00 K01 K10 K11 sx sy =
        (sx * sy) ^ 2 *
          xi_basepoint_scan_psl2r_covariance_gram2_det K00 K01 K10 K11) ∧
      (∀ Kxx Kxy Kyy sx sy : ℝ,
        sx ≠ 0 →
          sy ≠ 0 →
            Kxx ≠ 0 →
              Kyy ≠ 0 →
                xi_basepoint_scan_psl2r_covariance_normalized_correlation
                    (sx * sx * Kxx) (sx * sy * Kxy) (sy * sy * Kyy) =
                  xi_basepoint_scan_psl2r_covariance_normalized_correlation Kxx Kxy Kyy)

/-- Paper label: `prop:xi-basepoint-scan-psl2r-covariance`. -/
theorem paper_xi_basepoint_scan_psl2r_covariance :
    xi_basepoint_scan_psl2r_covariance_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b c d p x y hdet hp hx hy hxp hyp hmx hmy
    have hxscale :
        xi_basepoint_scan_psl2r_covariance_transformed_channel a b c d p x =
          (c * x + d) * (1 / (x - p)) := by
      have hxnum :
          a * d * x + (-(a * d * p) - b * c * x) + b * c * p ≠ 0 := by
        have hprod : (a * d - b * c) * (x - p) ≠ 0 := mul_ne_zero hdet hxp
        rwa [show (a * d - b * c) * (x - p) =
            a * d * x + (-(a * d * p) - b * c * x) + b * c * p by ring] at hprod
      unfold xi_basepoint_scan_psl2r_covariance_transformed_channel
        xi_basepoint_scan_psl2r_covariance_mobius
        xi_basepoint_scan_psl2r_covariance_delta at *
      field_simp [hdet, hp, hx, hxp, hmx, hxnum]
      rw [← mul_inv_cancel₀ hxnum]
      ring
    have hyscale :
        xi_basepoint_scan_psl2r_covariance_transformed_channel a b c d p y =
          (c * y + d) * (1 / (y - p)) := by
      have hynum :
          a * d * y + (-(a * d * p) - b * c * y) + b * c * p ≠ 0 := by
        have hprod : (a * d - b * c) * (y - p) ≠ 0 := mul_ne_zero hdet hyp
        rwa [show (a * d - b * c) * (y - p) =
            a * d * y + (-(a * d * p) - b * c * y) + b * c * p by ring] at hprod
      unfold xi_basepoint_scan_psl2r_covariance_transformed_channel
        xi_basepoint_scan_psl2r_covariance_mobius
        xi_basepoint_scan_psl2r_covariance_delta at *
      field_simp [hdet, hp, hy, hyp, hmy, hynum]
      rw [← mul_inv_cancel₀ hynum]
      ring
    unfold xi_basepoint_scan_psl2r_covariance_transformed_kernel
      xi_basepoint_scan_psl2r_covariance_cauchy_kernel
    rw [hxscale, hyscale]
    ring
  · intro K00 K01 K10 K11 sx sy
    unfold xi_basepoint_scan_psl2r_covariance_scaled_gram2_det
      xi_basepoint_scan_psl2r_covariance_gram2_det
    ring
  · intro Kxx Kxy Kyy sx sy hsx hsy hxx hyy
    unfold xi_basepoint_scan_psl2r_covariance_normalized_correlation
    field_simp [hsx, hsy, hxx, hyy]

end

end Omega.Zeta
