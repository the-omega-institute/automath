import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Zeta.UnitaryDeterminantZeroUnitCircle

namespace Omega.CircleDimension

private lemma normSq_sub_one (w : ℂ) :
    Complex.normSq (w - 1) = Complex.normSq w + 1 - 2 * Complex.re w := by
  simp [Complex.normSq_apply, sub_eq_add_neg]
  ring

private lemma normSq_add_one (w : ℂ) :
    Complex.normSq (w + 1) = Complex.normSq w + 1 + 2 * Complex.re w := by
  simp [Complex.normSq_apply]
  ring

/-- Paper-facing Schur contraction extracted from a Toeplitz/Carathéodory lower buffer.
    thm:cdim-toeplitz-gap-schur-contraction -/
theorem paper_cdim_toeplitz_gap_schur_contraction (delta r : ℝ) (C S : Complex → Complex)
    (hr : 0 < r ∧ r < 1) (hdelta : 0 < delta)
    (hbuffer : ∀ z, Complex.abs z ≤ r → delta ≤ Complex.re (C z))
    (hgrowth : ∀ z, Complex.abs z ≤ r → Complex.abs (C z) ≤ (1 + r) / (1 - r))
    (hS : ∀ z, S z = (C z - 1) / (C z + 1)) :
    ∀ z, Complex.abs z ≤ r → Complex.abs (S z) ≤ Real.sqrt (1 - delta * (1 - r)^2) := by
  intro z hz
  let M : ℝ := (1 + r) / (1 - r)
  have hr0 : 0 < r := hr.1
  have hr1 : r < 1 := hr.2
  have hOneSub_pos : 0 < 1 - r := by linarith
  have hOneSub_ne : 1 - r ≠ 0 := ne_of_gt hOneSub_pos
  have hM_add_one : M + 1 = 2 / (1 - r) := by
    dsimp [M]
    field_simp [hOneSub_ne]
    ring
  have hM_add_one_pos : 0 < M + 1 := by
    rw [hM_add_one]
    positivity
  have hRe : delta ≤ Complex.re (C z) := hbuffer z hz
  have hAbs : Complex.abs (C z) ≤ M := by
    simpa [M] using hgrowth z hz
  have hdelta_le_M : delta ≤ M := by
    exact hRe.trans <| (Complex.re_le_norm _).trans hAbs
  have hdelta_mul_le : delta * (1 - r) ^ 2 ≤ 1 - r ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_right hdelta_le_M (sq_nonneg (1 - r))
    have hrewrite : M * (1 - r) ^ 2 = 1 - r ^ 2 := by
      dsimp [M]
      field_simp [hOneSub_ne]
      ring
    simpa [hrewrite] using hmul
  have hsqrt_arg_nonneg : 0 ≤ 1 - delta * (1 - r) ^ 2 := by
    nlinarith [hdelta_mul_le, sq_nonneg r]
  have hden_re_pos : 0 < Complex.re (C z + 1) := by
    have htmp : delta + 1 ≤ Complex.re (C z + 1) := by
      simpa using add_le_add_right hRe 1
    linarith
  have hden_ne : C z + 1 ≠ 0 := by
    intro hzero
    have : Complex.re (C z + 1) = 0 := by simp [hzero]
    linarith
  have hplus_abs_le : Complex.abs (C z + 1) ≤ M + 1 := by
    calc
      Complex.abs (C z + 1) ≤ Complex.abs (C z) + Complex.abs (1 : ℂ) := by
        simpa using norm_add_le (C z) (1 : ℂ)
      _ ≤ M + 1 := by simpa using add_le_add_right hAbs 1
  have hden_sq_le : Complex.normSq (C z + 1) ≤ (M + 1) ^ 2 := by
    rw [Complex.normSq_eq_norm_sq]
    have hnorm_le : ‖C z + 1‖ ≤ M + 1 := by
      simpa [Complex.abs] using hplus_abs_le
    exact (sq_le_sq₀ (by positivity) hM_add_one_pos.le).2 hnorm_le
  have hratio_le_delta :
      Complex.normSq ((C z - 1) / (C z + 1)) ≤
        1 - 4 * delta / Complex.normSq (C z + 1) := by
    have hformula : Complex.normSq (C z - 1) = Complex.normSq (C z + 1) - 4 * Complex.re (C z) := by
      nlinarith [normSq_sub_one (C z), normSq_add_one (C z)]
    have hden_pos : 0 < Complex.normSq (C z + 1) := Complex.normSq_pos.2 hden_ne
    rw [Complex.normSq_div]
    apply (div_le_iff₀ hden_pos).2
    have hnum_le : Complex.normSq (C z - 1) ≤ Complex.normSq (C z + 1) - 4 * delta := by
      nlinarith [hformula, hRe]
    have hrewrite :
        (1 - 4 * delta / Complex.normSq (C z + 1)) * Complex.normSq (C z + 1) =
          Complex.normSq (C z + 1) - 4 * delta := by
      have hnormSq_ne : Complex.normSq (C z + 1) ≠ 0 := by
        intro hzero
        exact hden_ne (Complex.normSq_eq_zero.mp hzero)
      field_simp [hnormSq_ne]
    simpa [hrewrite] using hnum_le
  have hM_add_one_sq_pos : 0 < (M + 1) ^ 2 := by
    rw [hM_add_one]
    positivity
  have hfrac_le :
      4 * delta / (M + 1) ^ 2 ≤ 4 * delta / Complex.normSq (C z + 1) := by
    have hinv_le :
        1 / (M + 1) ^ 2 ≤ 1 / Complex.normSq (C z + 1) := by
      exact one_div_le_one_div_of_le (Complex.normSq_pos.2 hden_ne) hden_sq_le
    have hmul_nonneg : 0 ≤ 4 * delta := by nlinarith
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hinv_le hmul_nonneg
  have hratio_le_M :
      Complex.normSq ((C z - 1) / (C z + 1)) ≤ 1 - 4 * delta / (M + 1) ^ 2 := by
    have hcomp :
        1 - 4 * delta / Complex.normSq (C z + 1) ≤ 1 - 4 * delta / (M + 1) ^ 2 := by
      nlinarith
    exact hratio_le_delta.trans hcomp
  have hbound_rewrite : 1 - 4 * delta / (M + 1) ^ 2 = 1 - delta * (1 - r) ^ 2 := by
    rw [hM_add_one]
    field_simp [hOneSub_ne]
    ring
  have hsq :
      Complex.abs ((C z - 1) / (C z + 1)) ^ 2 ≤ 1 - delta * (1 - r) ^ 2 := by
    simpa only [Complex.abs, Complex.normSq_eq_norm_sq, hbound_rewrite] using hratio_le_M
  have hschur :
      Complex.abs ((C z - 1) / (C z + 1)) ≤ Real.sqrt (1 - delta * (1 - r) ^ 2) := by
    exact Real.le_sqrt_of_sq_le hsq
  simpa [hS z] using hschur

end Omega.CircleDimension
