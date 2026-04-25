import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Topology.Algebra.InfiniteSum.Basic
import Mathlib.Tactic
import Omega.Folding.FoldResonanceLadderFibLucLimits

open Filter
open scoped goldenRatio

namespace Omega.DerivedConsequences

noncomputable section

/-- The Fibonacci-side positive cluster constant. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point : ℝ :=
  (1 / Real.sqrt 5) ^ (2 : ℕ)

/-- The Lucas-side positive cluster constant. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point : ℝ :=
  1

/-- Concrete diagonal multiplier model: the Fibonacci cluster sits on even modes and the Lucas
cluster on odd modes. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (n : ℕ) : ℝ :=
  if Even n then
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point
  else
    derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point

/-- Essential-spectrum stand-in: the given value occurs infinitely often on the diagonal. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point (x : ℝ) : Prop :=
  ∀ N : ℕ, ∃ n ≥ N,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_diag n = x

/-- Noncompactness for the concrete diagonal model. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact : Prop :=
  ¬ Tendsto derived_golden_resonance_diagonal_multiplier_essential_clusters_diag atTop (nhds 0)

/-- Scalar-plus-compact exclusion for the concrete diagonal model. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_not_scalar_plus_compact :
    Prop :=
  ∀ l : ℝ,
    ¬ Tendsto
      (fun n =>
        derived_golden_resonance_diagonal_multiplier_essential_clusters_diag n - l)
      atTop (nhds 0)

/-- Natural-index Schatten exclusion for the concrete diagonal model. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_not_schatten
    (p : ℕ) : Prop :=
  ¬ Summable
    (fun n =>
      |derived_golden_resonance_diagonal_multiplier_essential_clusters_diag n| ^ p)

/-- Paper-facing package for the concrete diagonal multiplier model. -/
def derived_golden_resonance_diagonal_multiplier_essential_clusters_statement : Prop :=
  let fibPoint := derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point
  let lucPoint := derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point
  Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_alpha 0 1 ^ (2 : ℕ) = fibPoint ∧
    Omega.Folding.fold_resonance_ladder_fibonacci_directional_limit_alpha 2 1 ^ (2 : ℕ) =
      lucPoint ∧
    0 < fibPoint ∧
    0 < lucPoint ∧
    fibPoint ≠ lucPoint ∧
    derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point fibPoint ∧
    derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point lucPoint ∧
    derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact ∧
    derived_golden_resonance_diagonal_multiplier_essential_clusters_not_scalar_plus_compact ∧
    (∀ p : ℕ, 1 ≤ p →
      derived_golden_resonance_diagonal_multiplier_essential_clusters_not_schatten p)

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_even (n : ℕ) :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n) =
      derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point := by
  simp [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag]

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_odd (n : ℕ) :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n + 1) =
      derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point := by
  simp [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag]

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_pos :
    0 < derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point := by
  unfold derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point
  positivity

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_eq_one_fifth :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point = (1 / 5 : ℝ) := by
  unfold derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point
  have hsqrt5_sq : (Real.sqrt 5 : ℝ) ^ (2 : ℕ) = 5 := by
    nlinarith [Real.sq_sqrt (show 0 ≤ (5 : ℝ) by positivity)]
  calc
    (1 / Real.sqrt 5) ^ (2 : ℕ) = 1 / ((Real.sqrt 5 : ℝ) ^ (2 : ℕ)) := by
      field_simp [show (Real.sqrt 5 : ℝ) ≠ 0 by positivity]
    _ = (1 / 5 : ℝ) := by rw [hsqrt5_sq]

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point_pos :
    0 < derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point := by
  norm_num [derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point]

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_points_ne :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point ≠
      derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point := by
  rw [derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_eq_one_fifth,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point]
  norm_num

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul
    (n : ℕ) : n ≤ 2 * n := by
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using Nat.le_add_left n n

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul_add_one
    (n : ℕ) : n ≤ 2 * n + 1 := by
  simpa [two_mul, add_comm, add_left_comm, add_assoc] using Nat.le_add_left n (n + 1)

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_eventually :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point
      derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point := by
  intro N
  exact ⟨2 * N, by omega,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_even N⟩

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_eventually :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_essential_point
      derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point := by
  intro N
  exact ⟨2 * N + 1, by omega,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_odd N⟩

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact_true :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact := by
  intro h
  have hEven :
      Tendsto
        (fun n : ℕ =>
          derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n))
        atTop (nhds 0) := by
    exact h.comp
      (tendsto_atTop_mono
        derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul
        tendsto_id)
  have hconst : Tendsto (fun _ : ℕ =>
      derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point) atTop (nhds 0) := by
    simpa [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_even] using hEven
  have hzero :
      derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hconst
  exact
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_pos.ne' hzero

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_not_scalar_true :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_not_scalar_plus_compact := by
  intro l h
  have hEven :
      Tendsto
        (fun n : ℕ =>
          derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n) - l)
        atTop (nhds 0) := by
    exact h.comp
      (tendsto_atTop_mono
        derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul
        tendsto_id)
  have hOdd :
      Tendsto
        (fun n : ℕ =>
          derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n + 1) - l)
        atTop (nhds 0) := by
    exact h.comp
      (tendsto_atTop_mono
        derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul_add_one
        tendsto_id)
  have hEvenConst :
      Tendsto
        (fun _ : ℕ =>
          derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point - l)
        atTop (nhds 0) := by
    simpa [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_even] using hEven
  have hOddConst :
      Tendsto
        (fun _ : ℕ =>
          derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point - l)
        atTop (nhds 0) := by
    simpa [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_odd] using hOdd
  have hFibEq :
      derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point - l = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hEvenConst
  have hLucEq :
      derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point - l = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hOddConst
  exact derived_golden_resonance_diagonal_multiplier_essential_clusters_points_ne <| by
    linarith

private lemma derived_golden_resonance_diagonal_multiplier_essential_clusters_not_schatten_true
    (p : ℕ) (hp : 1 ≤ p) :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_not_schatten p := by
  intro hs
  have hEven :
      Tendsto
        (fun n : ℕ =>
          |derived_golden_resonance_diagonal_multiplier_essential_clusters_diag (2 * n)| ^ p)
        atTop (nhds 0) := by
    exact hs.tendsto_atTop_zero.comp
      (tendsto_atTop_mono
        derived_golden_resonance_diagonal_multiplier_essential_clusters_nat_le_two_mul
        tendsto_id)
  have hConst :
      Tendsto
        (fun _ : ℕ =>
          |derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point| ^ p)
        atTop (nhds 0) := by
    simpa [derived_golden_resonance_diagonal_multiplier_essential_clusters_diag_even] using hEven
  have hzero :
      |derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point| ^ p = 0 :=
    tendsto_nhds_unique tendsto_const_nhds hConst
  have hpow_pos :
      0 < |derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point| ^ p := by
    have habs_pos :
        0 < |derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point| := by
      exact abs_pos.mpr
        derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_pos.ne'
    exact pow_pos habs_pos p
  exact hpow_pos.ne' hzero

/-- Paper label: `thm:derived-golden-resonance-diagonal-multiplier-essential-clusters`. The
Fibonacci/Lucas directional-limit package provides two distinct positive cluster constants
`(1 / √5)^2` and `1`. Placing them on the even/odd diagonal modes yields a concrete model with two
essential points, hence noncompactness, scalar-plus-compact exclusion, and exclusion from every
natural-index Schatten class. -/
theorem paper_derived_golden_resonance_diagonal_multiplier_essential_clusters :
    derived_golden_resonance_diagonal_multiplier_essential_clusters_statement := by
  rcases Omega.Folding.paper_fold_resonance_ladder_fib_luc_limits with
    ⟨hαFib, _, hαLuc, _, _, _, _, _, _, _⟩
  exact ⟨by
      rw [hαFib, derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point],
    by
      rw [hαLuc, derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point]
      norm_num,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_point_pos,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_point_pos,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_points_ne,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_fib_eventually,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_luc_eventually,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_noncompact_true,
    derived_golden_resonance_diagonal_multiplier_essential_clusters_not_scalar_true,
    fun p hp =>
      derived_golden_resonance_diagonal_multiplier_essential_clusters_not_schatten_true p hp⟩

end

end Omega.DerivedConsequences
