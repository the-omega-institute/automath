import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

noncomputable section

/-- The geometric Taylor tail bound at radius `R` and boundary point `θ`. -/
def xiTaylorTailBound (M R θ : ℝ) (N : ℕ) : ℝ :=
  M / (1 - θ / R) * (θ / R) ^ (N + 1)

/-- The geometric derivative-tail bound coming from the weighted geometric series. -/
def xiDerivativeTailBound (M R θ : ℝ) (N : ℕ) : ℝ :=
  (M / R) * ((((N : ℝ) + 1) - (N : ℝ) * (θ / R)) / (1 - θ / R) ^ 2) * (θ / R) ^ N

/-- Strict sign agreement between the Taylor jet slope and the true derivative. -/
def xiSameSign (x y : ℝ) : Prop :=
  0 < x * y

/-- The finite Taylor-jet certificate consists of the value bound, the derivative bound,
and the resulting sign test for the derivative. -/
def xiFiniteTaylorJetCertificate
    (M R θ : ℝ) (N : ℕ) (valueError derivativeError taylorJetSlope : ℝ) : Prop :=
  |valueError| ≤ xiTaylorTailBound M R θ N ∧
    |derivativeError| ≤ xiDerivativeTailBound M R θ N ∧
    xiSameSign taylorJetSlope (taylorJetSlope + derivativeError)

private lemma xi_ratio_nonneg {R θ : ℝ} (hR : 0 < R) (hθ : 0 ≤ θ) : 0 ≤ θ / R := by
  exact div_nonneg hθ hR.le

private lemma xi_ratio_lt_one {R θ : ℝ} (hR : 0 < R) (hθR : θ < R) : θ / R < 1 := by
  exact (div_lt_one hR).2 hθR

private lemma xi_one_sub_ratio_pos {R θ : ℝ} (hR : 0 < R) (hθR : θ < R) : 0 < 1 - θ / R := by
  have hq : θ / R < 1 := xi_ratio_lt_one hR hθR
  linarith

private lemma xi_taylor_tail_bound_nonneg
    {M R θ : ℝ} {N : ℕ} (hM : 0 ≤ M) (hR : 0 < R) (hθ : 0 ≤ θ) (hθR : θ < R) :
    0 ≤ xiTaylorTailBound M R θ N := by
  unfold xiTaylorTailBound
  have hq_nonneg : 0 ≤ θ / R := xi_ratio_nonneg hR hθ
  have hden : 0 ≤ 1 - θ / R := le_of_lt (xi_one_sub_ratio_pos hR hθR)
  positivity

private lemma xi_derivative_numerator_pos
    {R θ : ℝ} {N : ℕ} (hR : 0 < R) (_hθ : 0 ≤ θ) (hθR : θ < R) :
    0 < ((N : ℝ) + 1) - (N : ℝ) * (θ / R) := by
  have hq_lt : θ / R < 1 := xi_ratio_lt_one hR hθR
  have hN : (0 : ℝ) ≤ N := by exact_mod_cast Nat.zero_le N
  nlinarith

private lemma xi_derivative_tail_bound_nonneg
    {M R θ : ℝ} {N : ℕ} (hM : 0 ≤ M) (hR : 0 < R) (hθ : 0 ≤ θ) (hθR : θ < R) :
    0 ≤ xiDerivativeTailBound M R θ N := by
  unfold xiDerivativeTailBound
  have hMR : 0 ≤ M / R := by exact div_nonneg hM hR.le
  have hnum : 0 ≤ ((N : ℝ) + 1) - (N : ℝ) * (θ / R) :=
    le_of_lt (xi_derivative_numerator_pos hR hθ hθR)
  have hq_nonneg : 0 ≤ θ / R := xi_ratio_nonneg hR hθ
  positivity

private lemma xi_sign_from_derivative_bound
    {M R θ derivativeError taylorJetSlope : ℝ} {N : ℕ}
    (hM : 0 ≤ M) (hR : 0 < R) (hθ : 0 ≤ θ) (hθR : θ < R)
    (hDeriv : |derivativeError| ≤ xiDerivativeTailBound M R θ N)
    (hSlope : xiDerivativeTailBound M R θ N < |taylorJetSlope|) :
    xiSameSign taylorJetSlope (taylorJetSlope + derivativeError) := by
  have hBoundNonneg : 0 ≤ xiDerivativeTailBound M R θ N :=
    xi_derivative_tail_bound_nonneg hM hR hθ hθR
  have hsmall : |derivativeError| < |taylorJetSlope| := lt_of_le_of_lt hDeriv hSlope
  by_cases hjet : 0 ≤ taylorJetSlope
  · have hjet_pos : 0 < taylorJetSlope := by
      by_contra hnot
      have hle0 : taylorJetSlope ≤ 0 := not_lt.mp hnot
      have hEq : taylorJetSlope = 0 := le_antisymm hle0 hjet
      rw [hEq, abs_zero] at hSlope
      exact not_lt_of_ge hBoundNonneg hSlope
    have herr : -taylorJetSlope < derivativeError ∧ derivativeError < taylorJetSlope := by
      rw [abs_of_nonneg hjet] at hsmall
      exact abs_lt.mp hsmall
    have hsum_pos : 0 < taylorJetSlope + derivativeError := by
      linarith
    unfold xiSameSign
    exact mul_pos hjet_pos hsum_pos
  · have hjet_neg : taylorJetSlope < 0 := lt_of_not_ge hjet
    have herr : taylorJetSlope < derivativeError ∧ derivativeError < -taylorJetSlope := by
      rw [abs_of_neg hjet_neg] at hsmall
      simpa using abs_lt.mp hsmall
    have hsum_neg : taylorJetSlope + derivativeError < 0 := by
      linarith
    unfold xiSameSign
    exact mul_pos_of_neg_of_neg hjet_neg hsum_neg

/-- The RH-boundary finite Taylor-jet certificate: once the Cauchy-style value and derivative
tails are controlled by the explicit geometric bounds, a strict derivative-margin test forces the
Taylor jet slope to have the same sign as the true derivative.
    thm:xi-time-part50be-rh-boundary-finite-taylor-jet-certificate -/
theorem paper_xi_time_part50be_rh_boundary_finite_taylor_jet_certificate
    (M R θ valueError derivativeError taylorJetSlope : ℝ) (N : ℕ)
    (hM : 0 ≤ M) (hR : 0 < R) (hθ : 0 ≤ θ) (hθR : θ < R)
    (hValue : |valueError| ≤ xiTaylorTailBound M R θ N)
    (hDeriv : |derivativeError| ≤ xiDerivativeTailBound M R θ N)
    (hSlope : xiDerivativeTailBound M R θ N < |taylorJetSlope|) :
    xiFiniteTaylorJetCertificate M R θ N valueError derivativeError taylorJetSlope ∧
      0 ≤ xiTaylorTailBound M R θ N ∧
      0 ≤ xiDerivativeTailBound M R θ N := by
  refine ⟨?_, xi_taylor_tail_bound_nonneg hM hR hθ hθR,
    xi_derivative_tail_bound_nonneg hM hR hθ hθR⟩
  refine ⟨hValue, hDeriv, ?_⟩
  exact xi_sign_from_derivative_bound hM hR hθ hθR hDeriv hSlope

end

end Omega.Zeta
