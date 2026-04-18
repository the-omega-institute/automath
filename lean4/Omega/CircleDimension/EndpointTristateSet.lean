import Mathlib.Tactic
import Omega.Discussion.ChebyshevAdams

open scoped BigOperators
open Omega.Discussion

namespace Omega.CircleDimension

/-- The truncated endpoint operator obtained by evaluating the completed power chain at `S = 0`.
    Each degree contributes the reciprocal weight `1 / d` times the endpoint value
    `g (C_d(0))`. -/
def endpointTruncatedPowOperator (M : ℕ) (g : ℤ → ℚ) : ℚ :=
  Finset.sum (Finset.Icc 1 M) fun d => (1 : ℚ) / (d : ℚ) * g (chebyAdams d 0)

/-- Odd-channel harmonic partial sum. -/
def endpointOddHarmonic (M : ℕ) : ℚ :=
  Finset.sum ((Finset.Icc 1 M).filter fun d => d % 2 = 1) fun d => (1 : ℚ) / (d : ℚ)

/-- `d ≡ 0 (mod 4)` channel harmonic partial sum. -/
def endpointZeroModFourHarmonic (M : ℕ) : ℚ :=
  Finset.sum ((Finset.Icc 1 M).filter fun d => d % 4 = 0) fun d => (1 : ℚ) / (d : ℚ)

/-- `d ≡ 2 (mod 4)` channel harmonic partial sum. -/
def endpointTwoModFourHarmonic (M : ℕ) : ℚ :=
  Finset.sum ((Finset.Icc 1 M).filter fun d => d % 4 = 2) fun d => (1 : ℚ) / (d : ℚ)

private theorem chebyAdams_at_zero_four_mul (q : ℕ) :
    chebyAdams (4 * q) 0 = 2 := by
  induction q with
  | zero =>
      simpa using chebyAdams_at_zero_values.1
  | succ q ih =>
      rw [show 4 * (q + 1) = 4 * q + 4 by omega, chebyAdams_at_zero_period4]
      exact ih

private theorem chebyAdams_at_zero_four_mul_add_one (q : ℕ) :
    chebyAdams (4 * q + 1) 0 = 0 := by
  induction q with
  | zero =>
      simpa using chebyAdams_at_zero_values.2.1
  | succ q ih =>
      rw [show 4 * (q + 1) + 1 = (4 * q + 1) + 4 by omega, chebyAdams_at_zero_period4]
      exact ih

private theorem chebyAdams_at_zero_four_mul_add_two (q : ℕ) :
    chebyAdams (4 * q + 2) 0 = -2 := by
  induction q with
  | zero =>
      simpa using chebyAdams_at_zero_values.2.2.1
  | succ q ih =>
      rw [show 4 * (q + 1) + 2 = (4 * q + 2) + 4 by omega, chebyAdams_at_zero_period4]
      exact ih

private theorem chebyAdams_at_zero_four_mul_add_three (q : ℕ) :
    chebyAdams (4 * q + 3) 0 = 0 := by
  induction q with
  | zero =>
      simpa using chebyAdams_at_zero_values.2.2.2
  | succ q ih =>
      rw [show 4 * (q + 1) + 3 = (4 * q + 3) + 4 by omega, chebyAdams_at_zero_period4]
      exact ih

private theorem chebyAdams_at_zero_of_mod4_zero (d : ℕ) (h : d % 4 = 0) :
    chebyAdams d 0 = 2 := by
  have hd : d = 4 * (d / 4) := by
    omega
  rw [hd]
  exact chebyAdams_at_zero_four_mul (d / 4)

private theorem chebyAdams_at_zero_of_mod4_two (d : ℕ) (h : d % 4 = 2) :
    chebyAdams d 0 = -2 := by
  have hd : d = 4 * (d / 4) + 2 := by
    omega
  rw [hd]
  exact chebyAdams_at_zero_four_mul_add_two (d / 4)

private theorem chebyAdams_at_zero_of_odd (d : ℕ) (hodd : d % 2 = 1) :
    chebyAdams d 0 = 0 := by
  have hlt : d % 4 < 4 := Nat.mod_lt d (by decide)
  have hcases : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · omega
  · have hd : d = 4 * (d / 4) + 1 := by
      omega
    rw [hd]
    exact chebyAdams_at_zero_four_mul_add_one (d / 4)
  · omega
  · have hd : d = 4 * (d / 4) + 3 := by
      omega
    rw [hd]
    exact chebyAdams_at_zero_four_mul_add_three (d / 4)

private theorem chebyAdams_at_zero_of_even_not_mod4_zero (d : ℕ) (heven : d % 2 ≠ 1)
    (hzero : d % 4 ≠ 0) : chebyAdams d 0 = -2 := by
  have hlt : d % 4 < 4 := Nat.mod_lt d (by decide)
  have hcases : d % 4 = 0 ∨ d % 4 = 1 ∨ d % 4 = 2 ∨ d % 4 = 3 := by
    omega
  rcases hcases with h0 | h1 | h2 | h3
  · exact False.elim (hzero h0)
  · exact False.elim (heven (by omega))
  · exact chebyAdams_at_zero_of_mod4_two d h2
  · exact False.elim (heven (by omega))

set_option maxHeartbeats 400000 in
/-- Paper-facing endpoint decomposition of the truncated power-chain operator at `S = 0`: the
Chebyshev-Adams endpoint values depend only on `d mod 4`, so the sum splits into the odd,
`0 mod 4`, and `2 mod 4` harmonic channels weighted by `g(0)`, `g(2)`, and `g(-2)`.
    prop:endpoint-mod4-channel-decomposition -/
theorem paper_endpoint_mod4_channel_decomposition (M : ℕ) (g : ℤ → ℚ) :
    endpointTruncatedPowOperator M g =
      endpointOddHarmonic M * g 0 +
        endpointZeroModFourHarmonic M * g 2 +
        endpointTwoModFourHarmonic M * g (-2) := by
  let s : Finset ℕ := Finset.Icc 1 M
  have hsummand :
      endpointTruncatedPowOperator M g =
        Finset.sum s fun d =>
          if d % 2 = 1 then
            (1 : ℚ) / (d : ℚ) * g 0
          else if d % 4 = 0 then
            (1 : ℚ) / (d : ℚ) * g 2
          else
            (1 : ℚ) / (d : ℚ) * g (-2) := by
    unfold endpointTruncatedPowOperator
    refine Finset.sum_congr rfl ?_
    intro d hd
    by_cases hodd : d % 2 = 1
    · simp [hodd, chebyAdams_at_zero_of_odd d hodd]
    · by_cases hzero : d % 4 = 0
      · simp [hodd, hzero, chebyAdams_at_zero_of_mod4_zero d hzero]
      · simp [hodd, hzero, chebyAdams_at_zero_of_even_not_mod4_zero d hodd hzero]
  rw [hsummand]
  have hsplit :
      Finset.sum s (fun d =>
        if d % 2 = 1 then
          (1 : ℚ) / (d : ℚ) * g 0
        else if d % 4 = 0 then
          (1 : ℚ) / (d : ℚ) * g 2
        else
          (1 : ℚ) / (d : ℚ) * g (-2)) =
      Finset.sum s (fun d =>
        (if d % 2 = 1 then (1 : ℚ) / (d : ℚ) * g 0 else 0) +
          (if d % 4 = 0 then (1 : ℚ) / (d : ℚ) * g 2 else 0) +
          (if d % 4 = 2 then (1 : ℚ) / (d : ℚ) * g (-2) else 0)) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    by_cases hodd : d % 2 = 1
    · have hnotZero : d % 4 ≠ 0 := by
        omega
      have hnotTwo : d % 4 ≠ 2 := by
        omega
      simp [hodd, hnotZero, hnotTwo]
    · by_cases hzero : d % 4 = 0
      · have hnotTwo : d % 4 ≠ 2 := by
          omega
        simp [hodd, hzero, hnotTwo]
      · have htwo : d % 4 = 2 := by
          have hlt : d % 4 < 4 := Nat.mod_lt d (by decide)
          omega
        simp [hodd, hzero, htwo]
  have hgrouped :
      Finset.sum s (fun d =>
        (if d % 2 = 1 then (1 : ℚ) / (d : ℚ) * g 0 else 0) +
          (if d % 4 = 0 then (1 : ℚ) / (d : ℚ) * g 2 else 0) +
          (if d % 4 = 2 then (1 : ℚ) / (d : ℚ) * g (-2) else 0)) =
      endpointOddHarmonic M * g 0 +
        endpointZeroModFourHarmonic M * g 2 +
        endpointTwoModFourHarmonic M * g (-2) := by
    unfold endpointOddHarmonic endpointZeroModFourHarmonic endpointTwoModFourHarmonic
    rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
    rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_filter]
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact hsplit.trans hgrouped

/-- If the endpoint observable vanishes at `0`, the odd channel disappears from the endpoint
decomposition, leaving only the two even residue classes modulo `4`.
    cor:endpoint-odd-channel-vanish -/
theorem paper_endpoint_odd_channel_vanish (M : ℕ) (g : ℤ → ℚ) (hg0 : g 0 = 0) :
    endpointTruncatedPowOperator M g =
      endpointZeroModFourHarmonic M * g 2 + endpointTwoModFourHarmonic M * g (-2) := by
  simpa [hg0] using paper_endpoint_mod4_channel_decomposition M g

/-- Paper-facing residue-class compression of the endpoint values `chebyAdams d 0`: odd `d`
contribute `0`, multiples of `4` contribute `2`, and the remaining even class contributes `-2`.
    cor:endpoint-tristate-compression -/
theorem paper_endpoint_tristate_compression (d : ℕ) (hd : 1 ≤ d) :
    (d % 2 = 1 → Omega.Discussion.chebyAdams d 0 = 0) ∧
      (d % 4 = 0 → Omega.Discussion.chebyAdams d 0 = 2) ∧
      (d % 4 = 2 → Omega.Discussion.chebyAdams d 0 = -2) := by
  let _ := hd
  refine ⟨chebyAdams_at_zero_of_odd d, chebyAdams_at_zero_of_mod4_zero d,
    chebyAdams_at_zero_of_mod4_two d⟩

end Omega.CircleDimension
