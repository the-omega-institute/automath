import Mathlib

namespace Omega.Zeta

/-- The `n`-th scale contribution coming from the explicit zero family
`((k + 1 / 2) * φ^(n + 2))_{k ≥ 0}`. -/
noncomputable def foldResonanceScaleTerm (R : ℝ) (n : ℕ) : ℕ :=
  Nat.floor (R / Real.goldenRatio ^ (n + 2) + 1 / 2)

/-- Truncated positive zero count up to `N` visible scales. -/
noncomputable def foldResonancePositiveZeroCountAux (R : ℝ) (N : ℕ) : ℕ :=
  Finset.sum (Finset.range N) fun n => foldResonanceScaleTerm R n

/-- Concrete positive zero count model used in this file. -/
noncomputable def foldResonancePositiveZeroCount (R : ℝ) : ℕ :=
  foldResonancePositiveZeroCountAux R (Nat.floor R + 1)

/-- The linear main term obtained by dropping the floors in the scale sum. -/
noncomputable def foldResonanceLinearMainTerm (R : ℝ) (N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) fun n => R / Real.goldenRatio ^ (n + 2)

/-- Concrete package for the self-similar floor-sum model: the count is given by the explicit
truncated floor sum, the scale terms shift by one under `R ↦ R / φ`, and the floor error is at
most linear in the number of retained scales. -/
def FoldResonanceZeroCountSpec (R : ℝ) : Prop :=
  let N := Nat.floor R
  foldResonancePositiveZeroCount R = foldResonancePositiveZeroCountAux R (N + 1) ∧
    (∀ n : ℕ, foldResonanceScaleTerm R (n + 1) = foldResonanceScaleTerm (R / Real.goldenRatio) n) ∧
    ((foldResonancePositiveZeroCountAux R (N + 1) : ℝ) ≤
      foldResonanceLinearMainTerm R (N + 1) + (N + 1))

private lemma foldResonanceScaleTerm_shift (R : ℝ) (n : ℕ) :
    foldResonanceScaleTerm R (n + 1) = foldResonanceScaleTerm (R / Real.goldenRatio) n := by
  have hφ0 : (Real.goldenRatio : ℝ) ≠ 0 := by positivity
  unfold foldResonanceScaleTerm
  congr 1
  calc
    R / Real.goldenRatio ^ (n + 1 + 2) + 1 / 2
        = R / Real.goldenRatio ^ (n + 3) + 1 / 2 := by ring_nf
    _ = R / (Real.goldenRatio * Real.goldenRatio ^ (n + 2)) + 1 / 2 := by
          rw [show n + 3 = (n + 2) + 1 by omega, pow_succ, mul_comm]
    _ = R / (Real.goldenRatio ^ (n + 2) * Real.goldenRatio) + 1 / 2 := by
          rw [mul_comm]
    _ = (R / Real.goldenRatio) / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
          field_simp [hφ0]

private lemma foldResonanceScaleTerm_linear_bound (R : ℝ) (hR0 : 0 ≤ R) (n : ℕ) :
    (foldResonanceScaleTerm R n : ℝ) ≤ R / Real.goldenRatio ^ (n + 2) + 1 := by
  have hterm_nonneg : 0 ≤ R / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
    have hpow_pos : 0 < Real.goldenRatio ^ (n + 2) := by
      positivity
    positivity
  have hfloor :
      (foldResonanceScaleTerm R n : ℝ) ≤ R / Real.goldenRatio ^ (n + 2) + 1 / 2 := by
    exact Nat.floor_le hterm_nonneg
  linarith

/-- Paper label: `thm:xi-fold-resonance-zero-count-selfsimilar-linear`. -/
theorem paper_xi_fold_resonance_zero_count_selfsimilar_linear
    (R : ℝ) (hR : 0 < R) : FoldResonanceZeroCountSpec R := by
  dsimp [FoldResonanceZeroCountSpec, foldResonancePositiveZeroCount]
  refine ⟨rfl, foldResonanceScaleTerm_shift R, ?_⟩
  calc
    (foldResonancePositiveZeroCountAux R (Nat.floor R + 1) : ℝ)
        = Finset.sum (Finset.range (Nat.floor R + 1)) fun n => (foldResonanceScaleTerm R n : ℝ) := by
            simp [foldResonancePositiveZeroCountAux]
    _ ≤ Finset.sum (Finset.range (Nat.floor R + 1))
          (fun n => R / Real.goldenRatio ^ (n + 2) + 1) := by
          gcongr with n hn
          exact foldResonanceScaleTerm_linear_bound R (le_of_lt hR) n
    _ = foldResonanceLinearMainTerm R (Nat.floor R + 1) + (Nat.floor R + 1) := by
          simp [foldResonanceLinearMainTerm, Finset.sum_add_distrib]

end Omega.Zeta
