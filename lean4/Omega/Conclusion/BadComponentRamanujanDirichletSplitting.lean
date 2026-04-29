import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `thm:conclusion-bad-component-ramanujan-dirichlet-splitting`. -/
theorem paper_conclusion_bad_component_ramanujan_dirichlet_splitting (q N : ℕ) (t u : ℚ) :
    let term : ℕ → ℚ := fun k => ((Nat.fib (k + 3) : ℚ) ^ q) * t ^ (k + 1);
    let c3 : ℕ → ℚ := fun k => if (k + 1) % 3 = 0 then 2 else -1;
    let χ3 : ℕ → ℚ :=
      fun k => if (k + 1) % 3 = 0 then 0 else if (k + 1) % 3 = 1 then 1 else -1;
    let Φ := ∑ k ∈ Finset.range N, term k;
    let R := ∑ k ∈ Finset.range N, c3 k * term k;
    let X := ∑ k ∈ Finset.range N, χ3 k * term k;
    let C := ∑ k ∈ Finset.range N, (if (k + 1) % 3 = 1 then 1 else 0) * term k;
    let B := ∑ k ∈ Finset.range N, (if (k + 1) % 3 = 1 then 0 else 1) * term k;
    C = (1 / 3) * Φ - (1 / 6) * R + (1 / 2) * X ∧
      B = (2 / 3) * Φ + (1 / 6) * R - (1 / 2) * X ∧
        B + u * C =
          ((2 + u) / 3) * Φ + ((1 - u) / 6) * R + ((u - 1) / 2) * X := by
  let term : ℕ → ℚ := fun k => ((Nat.fib (k + 3) : ℚ) ^ q) * t ^ (k + 1)
  let c3 : ℕ → ℚ := fun k => if (k + 1) % 3 = 0 then 2 else -1
  let χ3 : ℕ → ℚ :=
    fun k => if (k + 1) % 3 = 0 then 0 else if (k + 1) % 3 = 1 then 1 else -1
  let Φ := ∑ k ∈ Finset.range N, term k
  let R := ∑ k ∈ Finset.range N, c3 k * term k
  let X := ∑ k ∈ Finset.range N, χ3 k * term k
  let C := ∑ k ∈ Finset.range N, (if (k + 1) % 3 = 1 then 1 else 0) * term k
  let B := ∑ k ∈ Finset.range N, (if (k + 1) % 3 = 1 then 0 else 1) * term k
  change C = (1 / 3) * Φ - (1 / 6) * R + (1 / 2) * X ∧
    B = (2 / 3) * Φ + (1 / 6) * R - (1 / 2) * X ∧
      B + u * C = ((2 + u) / 3) * Φ + ((1 - u) / 6) * R + ((u - 1) / 2) * X
  have hCpoint (k : ℕ) :
      (if (k + 1) % 3 = 1 then (1 : ℚ) else 0) * term k =
        (1 / 3) * term k - (1 / 6) * (c3 k * term k) +
          (1 / 2) * (χ3 k * term k) := by
    have hlt : (k + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hcases : (k + 1) % 3 = 0 ∨ (k + 1) % 3 = 1 ∨ (k + 1) % 3 = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · simp [c3, χ3, h0]
      ring
    · simp [c3, χ3, h1]
      ring
    · simp [c3, χ3, h2]
      ring
  have hBpoint (k : ℕ) :
      (if (k + 1) % 3 = 1 then (0 : ℚ) else 1) * term k =
        (2 / 3) * term k + (1 / 6) * (c3 k * term k) -
          (1 / 2) * (χ3 k * term k) := by
    have hlt : (k + 1) % 3 < 3 := Nat.mod_lt _ (by norm_num)
    have hcases : (k + 1) % 3 = 0 ∨ (k + 1) % 3 = 1 ∨ (k + 1) % 3 = 2 := by
      omega
    rcases hcases with h0 | h1 | h2
    · simp [c3, χ3, h0]
      ring
    · simp [c3, χ3, h1]
      ring
    · simp [c3, χ3, h2]
      ring
  have hC : C = (1 / 3) * Φ - (1 / 6) * R + (1 / 2) * X := by
    calc
      C = ∑ k ∈ Finset.range N,
          ((1 / 3) * term k - (1 / 6) * (c3 k * term k) +
            (1 / 2) * (χ3 k * term k)) := by
        dsimp [C]
        exact Finset.sum_congr rfl (fun k _ => hCpoint k)
      _ = (1 / 3) * Φ - (1 / 6) * R + (1 / 2) * X := by
        simp [Φ, R, X, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  have hB : B = (2 / 3) * Φ + (1 / 6) * R - (1 / 2) * X := by
    calc
      B = ∑ k ∈ Finset.range N,
          ((2 / 3) * term k + (1 / 6) * (c3 k * term k) -
            (1 / 2) * (χ3 k * term k)) := by
        dsimp [B]
        exact Finset.sum_congr rfl (fun k _ => hBpoint k)
      _ = (2 / 3) * Φ + (1 / 6) * R - (1 / 2) * X := by
        simp [Φ, R, X, Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.mul_sum]
  refine ⟨hC, hB, ?_⟩
  rw [hB, hC]
  ring

end Omega.Conclusion
