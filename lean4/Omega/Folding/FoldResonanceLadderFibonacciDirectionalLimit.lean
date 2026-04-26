import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped Topology goldenRatio

namespace Omega.Folding

noncomputable section

def fold_resonance_ladder_fibonacci_directional_limit_alpha (u0 u1 : ℤ) : ℝ :=
  ((u1 : ℝ) - (u0 : ℝ) * Real.goldenConj) / Real.sqrt 5

def fold_resonance_ladder_fibonacci_directional_limit_beta (u0 u1 : ℤ) : ℝ :=
  ((u0 : ℝ) * Real.goldenRatio - (u1 : ℝ)) / Real.sqrt 5

def fold_resonance_ladder_fibonacci_directional_limit_seq (u0 u1 : ℤ) (n : ℕ) : ℝ :=
  fold_resonance_ladder_fibonacci_directional_limit_alpha u0 u1 * Real.goldenRatio ^ n +
    fold_resonance_ladder_fibonacci_directional_limit_beta u0 u1 * Real.goldenConj ^ n

/-- Paper label: `thm:fold-resonance-ladder-fibonacci-directional-limit`.
The Binet coefficients attached to the initial data generate the Fibonacci recurrence, and the two
standard directional scalings of that recurrence converge to the explicit `φ`-eigendirection. -/
theorem paper_fold_resonance_ladder_fibonacci_directional_limit (u0 u1 : ℤ) :
    fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 0 = (u0 : ℝ) ∧
      fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 1 = (u1 : ℝ) ∧
      (∀ n : ℕ,
        fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + 2) =
          fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + 1) +
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 n) ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 n /
              Real.goldenRatio ^ (n + k))
          atTop
          (𝓝
            (fold_resonance_ladder_fibonacci_directional_limit_alpha u0 u1 /
              Real.goldenRatio ^ k))) ∧
      (∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + k) /
              Real.goldenRatio ^ n)
          atTop
          (𝓝
            (fold_resonance_ladder_fibonacci_directional_limit_alpha u0 u1 *
              Real.goldenRatio ^ k))) := by
  let α : ℝ := fold_resonance_ladder_fibonacci_directional_limit_alpha u0 u1
  let β : ℝ := fold_resonance_ladder_fibonacci_directional_limit_beta u0 u1
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by positivity
  have hu0 :
      α + β = (u0 : ℝ) := by
    rw [show α = ((u1 : ℝ) - (u0 : ℝ) * Real.goldenConj) / Real.sqrt 5 by rfl]
    rw [show β = ((u0 : ℝ) * Real.goldenRatio - (u1 : ℝ)) / Real.sqrt 5 by rfl]
    field_simp [hsqrt5_ne]
    nlinarith [Real.goldenRatio_sub_goldenConj]
  have hu1 :
      α * Real.goldenRatio + β * Real.goldenConj = (u1 : ℝ) := by
    rw [show α = ((u1 : ℝ) - (u0 : ℝ) * Real.goldenConj) / Real.sqrt 5 by rfl]
    rw [show β = ((u0 : ℝ) * Real.goldenRatio - (u1 : ℝ)) / Real.sqrt 5 by rfl]
    field_simp [hsqrt5_ne]
    nlinarith [Real.goldenRatio_mul_goldenConj, Real.goldenRatio_sub_goldenConj]
  have hrec :
      ∀ n : ℕ,
        fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + 2) =
          fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + 1) +
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 n := by
    intro n
    unfold fold_resonance_ladder_fibonacci_directional_limit_seq
    calc
      α * Real.goldenRatio ^ (n + 2) + β * Real.goldenConj ^ (n + 2)
          = α * (Real.goldenRatio ^ n * Real.goldenRatio ^ 2) +
              β * (Real.goldenConj ^ n * Real.goldenConj ^ 2) := by
              rw [pow_add, pow_add]
      _ = α * (Real.goldenRatio ^ n * (Real.goldenRatio + 1)) +
            β * (Real.goldenConj ^ n * (Real.goldenConj + 1)) := by
              rw [Real.goldenRatio_sq, Real.goldenConj_sq]
      _ = (α * Real.goldenRatio ^ (n + 1) + β * Real.goldenConj ^ (n + 1)) +
            (α * Real.goldenRatio ^ n + β * Real.goldenConj ^ n) := by
              rw [pow_add, pow_add]
              ring
  have hpow :
      Tendsto (fun n : ℕ => (Real.goldenConj / Real.goldenRatio : ℝ) ^ n) atTop (𝓝 0) := by
    exact tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := Real.goldenConj / Real.goldenRatio) <| by
      rw [abs_div, div_lt_one (by positivity), abs_of_pos Real.goldenRatio_pos, abs_lt]
      ring_nf
      bound
  have htail :
      ∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 n /
              Real.goldenRatio ^ (n + k))
          atTop
          (𝓝 (α / Real.goldenRatio ^ k)) := by
    intro k
    have hrewrite :
        (fun n : ℕ =>
          fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 n /
            Real.goldenRatio ^ (n + k)) =
          fun n : ℕ => α / Real.goldenRatio ^ k + (β / Real.goldenRatio ^ k) *
            (Real.goldenConj / Real.goldenRatio : ℝ) ^ n := by
      funext n
      unfold fold_resonance_ladder_fibonacci_directional_limit_seq
      calc
        (α * Real.goldenRatio ^ n + β * Real.goldenConj ^ n) / Real.goldenRatio ^ (n + k)
            = (α * Real.goldenRatio ^ n + β * Real.goldenConj ^ n) /
                (Real.goldenRatio ^ n * Real.goldenRatio ^ k) := by
                rw [pow_add]
        _ = α / Real.goldenRatio ^ k +
              β * (Real.goldenConj ^ n / Real.goldenRatio ^ n) / Real.goldenRatio ^ k := by
              field_simp [pow_ne_zero n Real.goldenRatio_ne_zero, pow_ne_zero k Real.goldenRatio_ne_zero]
        _ = α / Real.goldenRatio ^ k +
              β * ((Real.goldenConj / Real.goldenRatio : ℝ) ^ n) / Real.goldenRatio ^ k := by
              rw [← div_pow]
        _ = α / Real.goldenRatio ^ k +
              (β / Real.goldenRatio ^ k) * (Real.goldenConj / Real.goldenRatio : ℝ) ^ n := by
              ring
    rw [hrewrite]
    simpa using (hpow.const_mul (β / Real.goldenRatio ^ k)).const_add (α / Real.goldenRatio ^ k)
  have hhead :
      ∀ k : ℕ,
        Tendsto
          (fun n : ℕ =>
            fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + k) /
              Real.goldenRatio ^ n)
          atTop
          (𝓝 (α * Real.goldenRatio ^ k)) := by
    intro k
    have hrewrite :
        (fun n : ℕ =>
          fold_resonance_ladder_fibonacci_directional_limit_seq u0 u1 (n + k) /
            Real.goldenRatio ^ n) =
          fun n : ℕ => α * Real.goldenRatio ^ k +
            (β * Real.goldenConj ^ k) * (Real.goldenConj / Real.goldenRatio : ℝ) ^ n := by
      funext n
      unfold fold_resonance_ladder_fibonacci_directional_limit_seq
      calc
        (α * Real.goldenRatio ^ (n + k) + β * Real.goldenConj ^ (n + k)) / Real.goldenRatio ^ n
            = (α * (Real.goldenRatio ^ n * Real.goldenRatio ^ k) +
                β * (Real.goldenConj ^ n * Real.goldenConj ^ k)) / Real.goldenRatio ^ n := by
                rw [pow_add, pow_add]
        _ = α * Real.goldenRatio ^ k +
              β * Real.goldenConj ^ k * (Real.goldenConj ^ n / Real.goldenRatio ^ n) := by
              field_simp [pow_ne_zero n Real.goldenRatio_ne_zero]
        _ = α * Real.goldenRatio ^ k +
              (β * Real.goldenConj ^ k) * (Real.goldenConj / Real.goldenRatio : ℝ) ^ n := by
              rw [← div_pow]
    rw [hrewrite]
    simpa using
      (hpow.const_mul (β * Real.goldenConj ^ k)).const_add (α * Real.goldenRatio ^ k)
  refine ⟨?_, ?_, hrec, ?_, ?_⟩
  · simpa [fold_resonance_ladder_fibonacci_directional_limit_seq, α, β] using hu0
  · simpa [fold_resonance_ladder_fibonacci_directional_limit_seq, α, β] using hu1
  · intro k
    simpa [fold_resonance_ladder_fibonacci_directional_limit_alpha, α] using htail k
  · intro k
    simpa [fold_resonance_ladder_fibonacci_directional_limit_alpha, α] using hhead k

end

end Omega.Folding
