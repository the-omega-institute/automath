import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Folding

/-- The `n`-th visible fold-side scale term coming from the explicit zero family
`((k + 1 / 2) * φ^(n + 2))_{k ≥ 0}`. -/
noncomputable def fold_resonance_zero_counting_linear_scale_term (R : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (R / Real.goldenRatio ^ (n + 2) + 1 / 2)

/-- Truncated positive zero count up to `N` visible scales on the fold side. -/
noncomputable def fold_resonance_zero_counting_linear_positive_zero_count_aux
    (R : ℝ) (N : ℕ) : ℕ :=
  Finset.sum (Finset.range N) fun n => fold_resonance_zero_counting_linear_scale_term R n

/-- The linear main term obtained by dropping the floors in the fold-side scale sum. -/
noncomputable def fold_resonance_zero_counting_linear_main_term (R : ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n => R / Real.goldenRatio ^ (n + 2)

/-- Fold-side zero-counting package: after truncating to the visible scales, the scale terms shift
under `R ↦ R / φ` and the resulting floor sum is bounded by the linear main term plus one unit per
retained scale. -/
def fold_resonance_zero_counting_linear_statement (R : ℝ) : Prop :=
  0 < R →
    let N := Nat.floor R
    (∀ n : ℕ,
      fold_resonance_zero_counting_linear_scale_term R (n + 1) =
        fold_resonance_zero_counting_linear_scale_term (R / Real.goldenRatio) n) ∧
      ((fold_resonance_zero_counting_linear_positive_zero_count_aux R (N + 1) : ℝ) ≤
        fold_resonance_zero_counting_linear_main_term R (N + 1) + (N + 1))

private lemma fold_resonance_zero_counting_linear_shift (R : ℝ) (n : ℕ) :
    fold_resonance_zero_counting_linear_scale_term R (n + 1) =
      fold_resonance_zero_counting_linear_scale_term (R / Real.goldenRatio) n := by
  have hphi0 : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
  unfold fold_resonance_zero_counting_linear_scale_term
  congr 1
  calc
    R / Real.goldenRatio ^ (n + 1 + 2) + 1 / 2 = R / Real.goldenRatio ^ (n + 3) + 1 / 2 := by
      ring_nf
    _ = R / (Real.goldenRatio * Real.goldenRatio ^ (n + 2)) + 1 / 2 := by
      rw [show n + 3 = (n + 2) + 1 by omega, pow_succ, mul_comm]
    _ = R / (Real.goldenRatio ^ (n + 2) * Real.goldenRatio) + 1 / 2 := by
      rw [mul_comm]
    _ = (R / Real.goldenRatio) / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
      field_simp [hphi0]

private lemma fold_resonance_zero_counting_linear_floor_bound (R : ℝ) (hR0 : 0 ≤ R) (n : ℕ) :
    (fold_resonance_zero_counting_linear_scale_term R n : ℝ) ≤
      R / Real.goldenRatio ^ (n + 2) + 1 := by
  have hterm_nonneg : 0 ≤ R / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
    have hpow_pos : 0 < Real.goldenRatio ^ (n + 2) := by positivity
    positivity
  have hfloor :
      (fold_resonance_zero_counting_linear_scale_term R n : ℝ) ≤
        R / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
    exact Nat.floor_le hterm_nonneg
  linarith

/-- Paper label: `cor:fold-resonance-zero-counting-linear`. -/
theorem paper_fold_resonance_zero_counting_linear (R : ℝ) :
    fold_resonance_zero_counting_linear_statement R := by
  intro hR
  dsimp [fold_resonance_zero_counting_linear_statement]
  refine ⟨fold_resonance_zero_counting_linear_shift R, ?_⟩
  calc
    (fold_resonance_zero_counting_linear_positive_zero_count_aux R (Nat.floor R + 1) : ℝ) =
        Finset.sum (Finset.range (Nat.floor R + 1))
          (fun n => (fold_resonance_zero_counting_linear_scale_term R n : ℝ)) := by
            simp [fold_resonance_zero_counting_linear_positive_zero_count_aux]
    _ ≤ Finset.sum (Finset.range (Nat.floor R + 1))
          (fun n => R / Real.goldenRatio ^ (n + 2) + 1) := by
            gcongr with n hn
            exact fold_resonance_zero_counting_linear_floor_bound R (le_of_lt hR) n
    _ = fold_resonance_zero_counting_linear_main_term R (Nat.floor R + 1) + (Nat.floor R + 1) := by
          simp [fold_resonance_zero_counting_linear_main_term, Finset.sum_add_distrib]

end Omega.Folding
