import Mathlib.Analysis.SpecificLimits.Fibonacci
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.POM

/-- Paper label: `prop:pom-max-fiber-split-ratio-finite-scale`. The Fibonacci split ratios
converge to `φ⁻¹`, and Binet's formula gives the finite-scale correction factor. -/
theorem paper_pom_max_fiber_split_ratio_finite_scale :
    Tendsto (fun k : ℕ => (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2)) atTop
      (nhds (Real.goldenRatio⁻¹)) ∧
    (∀ k : ℕ,
      (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2) =
        Real.goldenRatio⁻¹ *
          ((1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 1)) /
            (1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 2)))) := by
  constructor
  · have h :=
      tendsto_fib_div_fib_succ_atTop.comp (tendsto_add_atTop_nat (1 : ℕ))
    rw [Real.inv_goldenRatio]
    simpa [Function.comp_def, Nat.add_assoc] using h
  · intro k
    let φ : ℝ := Real.goldenRatio
    let ψ : ℝ := Real.goldenConj
    have hφ : φ ≠ 0 := Real.goldenRatio_ne_zero
    have hsqrt : Real.sqrt 5 ≠ 0 := by norm_num
    have hdenFib : (Nat.fib (k + 2) : ℝ) ≠ 0 := by
      exact_mod_cast (ne_of_gt (Nat.fib_pos.2 (by omega : 0 < k + 2)))
    have hψ : ψ = -φ⁻¹ := by
      dsimp [ψ, φ]
      linarith [Real.inv_goldenRatio]
    have hq : ψ / φ = -(φ⁻¹ ^ 2) := by
      rw [hψ]
      field_simp [hφ]
    have hpow1 : φ ^ (k + 1) ≠ 0 := pow_ne_zero _ hφ
    have hpow2 : φ ^ (k + 2) ≠ 0 := pow_ne_zero _ hφ
    have hfactor1 :
        φ ^ (k + 1) - ψ ^ (k + 1) =
          φ ^ (k + 1) * (1 - (ψ / φ) ^ (k + 1)) := by
      have hdiv : (ψ / φ) ^ (k + 1) = ψ ^ (k + 1) / φ ^ (k + 1) := by
        rw [div_pow]
      have hcancel :
          φ ^ (k + 1) * (ψ ^ (k + 1) / φ ^ (k + 1)) = ψ ^ (k + 1) := by
        field_simp [hpow1]
      calc
        φ ^ (k + 1) - ψ ^ (k + 1)
            = φ ^ (k + 1) - φ ^ (k + 1) * (ψ ^ (k + 1) / φ ^ (k + 1)) := by
              rw [hcancel]
        _ = φ ^ (k + 1) * (1 - ψ ^ (k + 1) / φ ^ (k + 1)) := by ring
        _ = φ ^ (k + 1) * (1 - (ψ / φ) ^ (k + 1)) := by rw [hdiv]
    have hfactor2 :
        φ ^ (k + 2) - ψ ^ (k + 2) =
          φ ^ (k + 2) * (1 - (ψ / φ) ^ (k + 2)) := by
      have hdiv : (ψ / φ) ^ (k + 2) = ψ ^ (k + 2) / φ ^ (k + 2) := by
        rw [div_pow]
      have hcancel :
          φ ^ (k + 2) * (ψ ^ (k + 2) / φ ^ (k + 2)) = ψ ^ (k + 2) := by
        field_simp [hpow2]
      calc
        φ ^ (k + 2) - ψ ^ (k + 2)
            = φ ^ (k + 2) - φ ^ (k + 2) * (ψ ^ (k + 2) / φ ^ (k + 2)) := by
              rw [hcancel]
        _ = φ ^ (k + 2) * (1 - ψ ^ (k + 2) / φ ^ (k + 2)) := by ring
        _ = φ ^ (k + 2) * (1 - (ψ / φ) ^ (k + 2)) := by rw [hdiv]
    have hbinet1 :
        (Nat.fib (k + 1) : ℝ) =
          φ ^ (k + 1) * (1 - (ψ / φ) ^ (k + 1)) / Real.sqrt 5 := by
      dsimp [φ, ψ] at hfactor1 ⊢
      rw [Real.coe_fib_eq, hfactor1]
    have hbinet2 :
        (Nat.fib (k + 2) : ℝ) =
          φ ^ (k + 2) * (1 - (ψ / φ) ^ (k + 2)) / Real.sqrt 5 := by
      dsimp [φ, ψ] at hfactor2 ⊢
      rw [Real.coe_fib_eq, hfactor2]
    have hdenCorr : 1 - (ψ / φ) ^ (k + 2) ≠ 0 := by
      intro hzero
      apply hdenFib
      rw [hbinet2, hzero]
      ring
    calc
      (Nat.fib (k + 1) : ℝ) / Nat.fib (k + 2)
          = (φ ^ (k + 1) * (1 - (ψ / φ) ^ (k + 1)) / Real.sqrt 5) /
              (φ ^ (k + 2) * (1 - (ψ / φ) ^ (k + 2)) / Real.sqrt 5) := by
            rw [hbinet1, hbinet2]
      _ = φ⁻¹ * ((1 - (ψ / φ) ^ (k + 1)) / (1 - (ψ / φ) ^ (k + 2))) := by
            field_simp [hsqrt, hφ, hpow1, hpow2, hdenCorr]
            ring
      _ = Real.goldenRatio⁻¹ *
            ((1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 1)) /
              (1 - (-((Real.goldenRatio⁻¹) ^ 2)) ^ (k + 2))) := by
            dsimp [φ] at hq ⊢
            rw [hq]

end Omega.POM
