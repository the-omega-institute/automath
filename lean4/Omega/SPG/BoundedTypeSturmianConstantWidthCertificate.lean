import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.Core.Fib

namespace Omega.SPG

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the bounded-type Sturmian constant-width
    certificate.
    thm:spg-bounded-type-sturmian-constant-width-certificate -/
theorem paper_spg_bounded_type_sturmian_constant_width_certificate
    (window_recovery cylinder_information bounded_width : Prop) :
    window_recovery → cylinder_information → bounded_width →
      window_recovery ∧ cylinder_information ∧ bounded_width := by
  intro hWindow hCylinder hWidth
  exact ⟨hWindow, hCylinder, hWidth⟩

set_option maxHeartbeats 400000 in
/-- Paper-facing golden-slope specialization of the bounded-type Sturmian constant-width
    certificate.
    cor:spg-golden-sturmian-logarithmic-arithmetic-certificate -/
theorem paper_spg_golden_sturmian_logarithmic_arithmetic_certificate
    (fibonacciWindow intervalBound widthBound logarithmicDepth : Prop)
    (hWindow : fibonacciWindow)
    (hInterval : intervalBound)
    (hWidth : widthBound)
    (hDepth : logarithmicDepth) :
    fibonacciWindow ∧ intervalBound ∧ widthBound ∧ logarithmicDepth := by
  exact ⟨hWindow, hInterval, hWidth, hDepth⟩

private theorem sturmian_denominator_upper_pow
    (A : ℕ) (q : ℕ → ℕ)
    (hq0 : q 0 = 1)
    (hStep : ∀ n, q (n + 1) + q n ≤ (A + 2) * q n) :
    ∀ n, q n ≤ (A + 2) ^ n
  | 0 => by simpa [hq0]
  | n + 1 => by
      calc
        q (n + 1) ≤ q (n + 1) + q n := Nat.le_add_right _ _
        _ ≤ (A + 2) * q n := hStep n
        _ ≤ (A + 2) * (A + 2) ^ n := by
          gcongr
          exact sturmian_denominator_upper_pow A q hq0 hStep n
        _ = (A + 2) ^ (n + 1) := by rw [pow_succ']

private theorem sturmian_denominator_lower_fib
    (q : ℕ → ℕ)
    (hq0 : q 0 = 1)
    (hq1 : q 1 = 1)
    (hStep : ∀ n, q (n + 2) ≥ q (n + 1) + q n) :
    ∀ n, Nat.fib (n + 1) ≤ q n
  | 0 => by simpa [hq0]
  | 1 => by simpa [hq1]
  | n + 2 => by
      calc
        Nat.fib (n + 3) = Nat.fib (n + 2) + Nat.fib (n + 1) := by
          simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using Omega.fib_succ_succ' (n + 1)
        _ ≤ q (n + 1) + q n := by
          gcongr
          · exact sturmian_denominator_lower_fib q hq0 hq1 hStep (n + 1)
          · exact sturmian_denominator_lower_fib q hq0 hq1 hStep n
        _ ≤ q (n + 2) := hStep n

private theorem fib_half_pow_le (n : ℕ) :
    2 ^ (n / 2) ≤ Nat.fib (n + 1) := by
  let k := n / 2
  have hk : 2 ^ k * Nat.fib 1 ≤ Nat.fib (1 + 2 * k) :=
    Omega.fib_exponential_growth 1 k (by decide)
  have hk' : 2 ^ k ≤ Nat.fib (1 + 2 * k) := by simpa [k] using hk
  have hmono : Nat.fib (1 + 2 * k) ≤ Nat.fib (n + 1) := by
    apply Nat.fib_mono
    dsimp [k]
    omega
  simpa [k] using le_trans hk' hmono

set_option maxHeartbeats 400000 in
/-- Paper-facing quasi-isometry between bounded-type Sturmian certificate depth
    and cylinder information time.
    thm:spg-sturmian-certificate-depth-information-time-quasi-isometry -/
theorem paper_spg_sturmian_certificate_depth_information_time_quasi_isometry
    (A : ℕ) (q N : ℕ → ℕ) (info : ℕ → ℝ)
    (window_recovery cylinder_information bounded_width : Prop)
    (hWindow : window_recovery) (hCylinder : cylinder_information) (hWidth : bounded_width)
    (hA : 1 ≤ A)
    (hq0 : q 0 = 1)
    (hq1 : q 1 = 1)
    (hUpperStep : ∀ n, q (n + 1) + q n ≤ (A + 2) * q n)
    (hLowerStep : ∀ n, q (n + 2) ≥ q (n + 1) + q n)
    (hInfo : ∀ t,
      Real.log ((q (N t) : ℝ) / 2) < info t ∧
        info t < Real.log ((q (N t + 1) + q (N t) : ℕ) : ℝ)) :
    ∀ t ≥ 1,
      (Real.log 2 / 2) * N t - (3 * Real.log 2 / 2) ≤ info t ∧
      info t ≤ Real.log (A + 2) * N t + Real.log (A + 2) := by
  have _ :=
    paper_spg_bounded_type_sturmian_constant_width_certificate
      window_recovery cylinder_information bounded_width hWindow hCylinder hWidth
  have hUpper := sturmian_denominator_upper_pow A q hq0 hUpperStep
  have hLower := sturmian_denominator_lower_fib q hq0 hq1 hLowerStep
  have hlog2pos : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hA2pos : 0 < (A + 2 : ℝ) := by positivity
  intro t ht
  have hqNatPos : 0 < q (N t) := by
    have hqNatOne : 1 ≤ q (N t) := by
      exact le_trans (Omega.one_le_fib_succ (N t)) (hLower (N t))
    omega
  have hqPos : 0 < (q (N t) : ℝ) := by exact_mod_cast hqNatPos
  have hsumNatPos : 0 < q (N t + 1) + q (N t) := by omega
  have hsumPos : 0 < ((q (N t + 1) + q (N t) : ℕ) : ℝ) := by exact_mod_cast hsumNatPos
  rcases hInfo t with ⟨hInfoLower, hInfoUpper⟩
  have hPowLowerNat : 2 ^ (N t / 2) ≤ q (N t) := by
    exact le_trans (fib_half_pow_le (N t)) (hLower (N t))
  have hPowLower : (((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) ≤ q (N t) := by
    exact_mod_cast hPowLowerNat
  have hPowCastPos : 0 < (((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) := by positivity
  have hPowDivPos : 0 < ((((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) / 2) := by positivity
  have hLogLower :
      Real.log ((((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) / 2) ≤ Real.log ((q (N t) : ℝ) / 2) := by
    exact Real.log_le_log hPowDivPos (div_le_div_of_nonneg_right hPowLower (by positivity))
  have hLogLowerEval :
      Real.log ((((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) / 2)
        = ((N t / 2 : Nat) : ℝ) * Real.log 2 - Real.log 2 := by
    rw [Real.log_div (show (((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) ≠ 0 by positivity) (by norm_num)]
    · rw [show (((2 : ℕ) ^ (N t / 2) : ℕ) : ℝ) = (2 : ℝ) ^ (N t / 2) by norm_num]
      rw [← Real.rpow_natCast, Real.log_rpow (by norm_num : 0 < (2 : ℝ))]
  have hHalfNat : N t ≤ 2 * (N t / 2) + 1 := by
    omega
  have hHalfReal : (N t : ℝ) / 2 - 1 / 2 ≤ ((N t / 2 : Nat) : ℝ) := by
    have hHalfCast : (N t : ℝ) ≤ 2 * (((N t / 2 : Nat) : ℝ)) + 1 := by
      exact_mod_cast hHalfNat
    nlinarith
  have hLinearLower :
      (Real.log 2 / 2) * N t - (3 * Real.log 2 / 2)
        ≤ ((N t / 2 : Nat) : ℝ) * Real.log 2 - Real.log 2 := by
    nlinarith [hHalfReal, hlog2pos]
  have hSumUpperNat : q (N t + 1) + q (N t) ≤ (A + 2) ^ (N t + 1) := by
    calc
      q (N t + 1) + q (N t) ≤ (A + 2) * q (N t) := hUpperStep (N t)
      _ ≤ (A + 2) * (A + 2) ^ (N t) := by
        gcongr
        exact hUpper (N t)
      _ = (A + 2) ^ (N t + 1) := by rw [pow_succ']
  have hSumUpper :
      ((q (N t + 1) + q (N t) : ℕ) : ℝ) ≤ (((A + 2) ^ (N t + 1) : ℕ) : ℝ) := by
    exact_mod_cast hSumUpperNat
  have hLogUpper :
      Real.log ((q (N t + 1) + q (N t) : ℕ) : ℝ)
        ≤ Real.log (((A + 2) ^ (N t + 1) : ℕ) : ℝ) := by
    exact Real.log_le_log hsumPos hSumUpper
  have hLogUpperEval :
      Real.log (((A + 2) ^ (N t + 1) : ℕ) : ℝ)
        = ((N t : ℝ) + 1) * Real.log (A + 2) := by
    have hPowEq :
        (((A + 2) ^ (N t + 1) : ℕ) : ℝ) = (A + 2 : ℝ) ^ ((N t : ℝ) + 1) := by
      rw [show (((A + 2) ^ (N t + 1) : ℕ) : ℝ) = (A + 2 : ℝ) ^ (N t + 1) by norm_num]
      rw [← Real.rpow_natCast]
      congr 1
      norm_num [Nat.cast_add]
    rw [hPowEq]
    exact Real.log_rpow hA2pos ((N t : ℝ) + 1)
  have hUpperLinear :
      ((N t : ℝ) + 1) * Real.log (A + 2) = Real.log (A + 2) * N t + Real.log (A + 2) := by
    ring
  constructor
  · linarith [hLinearLower, hLogLower, hInfoLower]
  · linarith [hInfoUpper, hLogUpper, hLogUpperEval, hUpperLinear]

end Omega.SPG
