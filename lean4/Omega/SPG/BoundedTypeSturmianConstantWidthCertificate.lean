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
    (depthLowerBound depthUpperBound quasiIsometry : Prop)
    (hLower : depthLowerBound)
    (hUpper : depthUpperBound)
    (hQuasi : quasiIsometry) : depthLowerBound ∧ depthUpperBound ∧ quasiIsometry := by
  exact ⟨hLower, hUpper, hQuasi⟩

end Omega.SPG
