import Mathlib

namespace Omega.UnitCirclePhaseArithmetic

noncomputable section

/-- The explicit derivative of the two-term Laurent map `w ↦ A w^M + B w^N` on `ℂˣ`. -/
def twoTermLaurentDerivative (A B : ℂ) (M N : ℕ) (w : ℂ) : ℂ :=
  (A * (M : ℂ)) * w ^ (M - 1) + (B * (N : ℂ)) * w ^ (N - 1)

/-- The critical-value parameter `-BN / (AM)` controlling the singular ring. -/
def twoTermLaurentCriticalRatio (A B : ℂ) (M N : ℕ) : ℂ :=
  -((B * (N : ℂ)) / (A * (M : ℂ)))

private lemma twoTermLaurentDerivative_factor
    (A B : ℂ) (M N : ℕ) (w : ℂ) (hN : 1 ≤ N) (hMN : N < M) :
    twoTermLaurentDerivative A B M N w =
      w ^ (N - 1) * ((A * (M : ℂ)) * w ^ (M - N) + B * (N : ℂ)) := by
  have hpow : w ^ (M - 1) = w ^ (N - 1) * w ^ (M - N) := by
    rw [show M - 1 = (N - 1) + (M - N) by omega, pow_add]
  unfold twoTermLaurentDerivative
  rw [hpow]
  ring

/-- Differentiating the two-term Laurent map factors off `w^(N-1)`, so on `ℂˣ` the critical-point
equation is exactly `w^(M-N) = -BN / (AM)`. Taking norms yields the singular-ring equation
`‖w‖^(M-N) = ‖-BN/(AM)‖`. -/
theorem paper_derived_two_term_laurent_singular_ring
    (A B w : ℂ) (M N : ℕ) (hw : w ≠ 0) (hA : A ≠ 0) (_hB : B ≠ 0)
    (hN : 1 ≤ N) (hMN : N < M) :
    twoTermLaurentDerivative A B M N w = 0 ↔
      w ^ (M - N) = twoTermLaurentCriticalRatio A B M N ∧
        ‖w‖ ^ (M - N) = ‖twoTermLaurentCriticalRatio A B M N‖ := by
  have hM0_nat : M ≠ 0 := by omega
  have hN0_nat : N ≠ 0 := by omega
  have hM0 : (M : ℂ) ≠ 0 := by
    exact_mod_cast hM0_nat
  have hN0 : (N : ℂ) ≠ 0 := by
    exact_mod_cast hN0_nat
  have hwpow : w ^ (N - 1) ≠ 0 := pow_ne_zero _ hw
  have hcoeff : A * (M : ℂ) ≠ 0 := mul_ne_zero hA hM0
  constructor
  · intro hderiv
    have hfactor : w ^ (N - 1) * ((A * (M : ℂ)) * w ^ (M - N) + B * (N : ℂ)) = 0 := by
      simpa [twoTermLaurentDerivative_factor A B M N w hN hMN] using hderiv
    have hin : (A * (M : ℂ)) * w ^ (M - N) + B * (N : ℂ) = 0 := by
      exact (mul_eq_zero.mp hfactor).resolve_left hwpow
    have hcrit :
        w ^ (M - N) = twoTermLaurentCriticalRatio A B M N := by
      have hmulEq : (A * (M : ℂ)) * w ^ (M - N) = -(B * (N : ℂ)) := by
        rw [eq_neg_iff_add_eq_zero]
        exact hin
      unfold twoTermLaurentCriticalRatio
      have hcrit' : w ^ (M - N) = (-(B * (N : ℂ))) / (A * (M : ℂ)) := by
        apply (eq_div_iff hcoeff).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hmulEq
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using hcrit'
    have hnorm : ‖w‖ ^ (M - N) = ‖twoTermLaurentCriticalRatio A B M N‖ := by
      simpa [twoTermLaurentCriticalRatio, Complex.norm_pow] using congrArg norm hcrit
    exact ⟨hcrit, hnorm⟩
  · rintro ⟨hcrit, hnorm⟩
    have hin : (A * (M : ℂ)) * w ^ (M - N) + B * (N : ℂ) = 0 := by
      rw [hcrit, twoTermLaurentCriticalRatio]
      field_simp [hcoeff]
      ring
    rw [twoTermLaurentDerivative_factor A B M N w hN hMN]
    rw [hin]
    simp

end

end Omega.UnitCirclePhaseArithmetic
