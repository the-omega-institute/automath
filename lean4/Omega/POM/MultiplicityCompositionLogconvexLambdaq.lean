import Mathlib
import Omega.POM.MultiplicityCompositionMomentHierarchyRationalGrowth

namespace Omega.POM

noncomputable section

/-- The multiplicity-composition growth constant `λ_q` extracted from the moment hierarchy. -/
def pomMultiplicityCompositionLambda (q : ℕ) : ℝ :=
  pomMomentHierarchyDominantRoot q

/-- The secant slope of `q ↦ log λ_q` measured from the base point `q = 1`. -/
def pomMultiplicityCompositionLambdaSecantSlope (q : ℕ) : ℝ :=
  (Real.log (pomMultiplicityCompositionLambda q) - Real.log (pomMultiplicityCompositionLambda 1)) /
    ((q : ℝ) - 1)

/-- The Rényi entropy-rate proxy `log λ₁ - s_q`, where `s_q` is the secant slope from `q = 1`. -/
def pomMultiplicityCompositionRenyiEntropyRate (q : ℕ) : ℝ :=
  Real.log (pomMultiplicityCompositionLambda 1) - pomMultiplicityCompositionLambdaSecantSlope q

/-- Forward difference of the logarithmic growth constants. -/
def pomMultiplicityCompositionForwardDiff (q : ℕ) : ℝ :=
  Real.log (pomMultiplicityCompositionLambda (q + 1)) - Real.log (pomMultiplicityCompositionLambda q)

private lemma lambda_pos (q : ℕ) : 0 < pomMultiplicityCompositionLambda q := by
  have h := paper_pom_multiplicity_composition_moment_hierarchy_rational_growth
  exact (h.2.2.2.1 q).2.2

private lemma secant_two_eq :
    pomMultiplicityCompositionLambdaSecantSlope 2 = pomMultiplicityCompositionForwardDiff 1 := by
  unfold pomMultiplicityCompositionLambdaSecantSlope pomMultiplicityCompositionForwardDiff
  norm_num

private lemma secant_succ_recurrence (q : ℕ) (hq : 2 ≤ q) :
    (q : ℝ) * pomMultiplicityCompositionLambdaSecantSlope (q + 1) =
      ((q : ℝ) - 1) * pomMultiplicityCompositionLambdaSecantSlope q +
        pomMultiplicityCompositionForwardDiff q := by
  unfold pomMultiplicityCompositionLambdaSecantSlope pomMultiplicityCompositionForwardDiff
    pomMultiplicityCompositionLambda
  have hq0 : (q : ℝ) ≠ 0 := by positivity
  have hq1 : (q : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < q := by exact_mod_cast hq
    linarith
  have hqsub : ((((q + 1 : ℕ) : ℝ) - 1)) = (q : ℝ) := by
    norm_num
  rw [hqsub]
  field_simp [hq0, hq1]
  ring

private lemma logconvex_log_ineq
    (hlogconvex : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) ≤
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    2 * Real.log (pomMultiplicityCompositionLambda q) ≤
      Real.log (pomMultiplicityCompositionLambda (q - 1)) +
        Real.log (pomMultiplicityCompositionLambda (q + 1)) := by
  have hLm1_pos := lambda_pos (q - 1)
  have hL_pos := lambda_pos q
  have hLp1_pos := lambda_pos (q + 1)
  have hmain := hlogconvex q hq
  have hlog := Real.log_le_log (pow_pos hL_pos 2) hmain
  rw [pow_two, Real.log_mul (ne_of_gt hL_pos) (ne_of_gt hL_pos)] at hlog
  rw [Real.log_mul (ne_of_gt hLm1_pos) (ne_of_gt hLp1_pos)] at hlog
  simpa [two_mul] using hlog

private lemma forwardDiff_mono
    (hlogconvex : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) ≤
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    pomMultiplicityCompositionForwardDiff (q - 1) ≤ pomMultiplicityCompositionForwardDiff q := by
  have hlog := logconvex_log_ineq hlogconvex q hq
  have hq1 : 1 ≤ q := by omega
  have hineq :
      Real.log (pomMultiplicityCompositionLambda q) -
          Real.log (pomMultiplicityCompositionLambda (q - 1)) ≤
        Real.log (pomMultiplicityCompositionLambda (q + 1)) -
          Real.log (pomMultiplicityCompositionLambda q) := by
    linarith
  simpa [pomMultiplicityCompositionForwardDiff, Nat.sub_add_cancel hq1] using hineq

private lemma forwardDiff_strict_mono
    (hstrict : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) <
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    pomMultiplicityCompositionForwardDiff (q - 1) < pomMultiplicityCompositionForwardDiff q := by
  have hLm1_pos := lambda_pos (q - 1)
  have hL_pos := lambda_pos q
  have hLp1_pos := lambda_pos (q + 1)
  have hmain := hstrict q hq
  have hlog := Real.log_lt_log (pow_pos hL_pos 2) hmain
  rw [pow_two, Real.log_mul (ne_of_gt hL_pos) (ne_of_gt hL_pos)] at hlog
  rw [Real.log_mul (ne_of_gt hLm1_pos) (ne_of_gt hLp1_pos)] at hlog
  have hq1 : 1 ≤ q := by omega
  have hineq :
      Real.log (pomMultiplicityCompositionLambda q) -
          Real.log (pomMultiplicityCompositionLambda (q - 1)) <
        Real.log (pomMultiplicityCompositionLambda (q + 1)) -
          Real.log (pomMultiplicityCompositionLambda q) := by
    linarith
  simpa [pomMultiplicityCompositionForwardDiff, Nat.sub_add_cancel hq1] using hineq

private lemma secant_le_forwardDiff
    (hlogconvex : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) ≤
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1)) :
    ∀ n : ℕ,
      pomMultiplicityCompositionLambdaSecantSlope (n + 2) ≤
        pomMultiplicityCompositionForwardDiff (n + 2)
  | 0 => by
      rw [secant_two_eq]
      simpa using forwardDiff_mono hlogconvex 2 (by omega)
  | n + 1 => by
      have ih := secant_le_forwardDiff hlogconvex n
      have hrec := secant_succ_recurrence (n + 2) (by omega)
      have hq_pos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
      have hcoeff_nonneg : 0 ≤ (((n + 2 : ℕ) : ℝ) - 1) := by
        have hge : (1 : ℝ) ≤ ((n + 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ n + 2 by omega)
        linarith
      have hih :
          (((n + 2 : ℕ) : ℝ) - 1) * pomMultiplicityCompositionLambdaSecantSlope (n + 2) ≤
            (((n + 2 : ℕ) : ℝ) - 1) * pomMultiplicityCompositionForwardDiff (n + 2) := by
        exact mul_le_mul_of_nonneg_left ih hcoeff_nonneg
      have hmul :
          ((n + 2 : ℕ) : ℝ) * pomMultiplicityCompositionLambdaSecantSlope (n + 3) ≤
            ((n + 2 : ℕ) : ℝ) * pomMultiplicityCompositionForwardDiff (n + 2) := by
        nlinarith [hrec, hih]
      have htmp : pomMultiplicityCompositionLambdaSecantSlope (n + 3) ≤
          pomMultiplicityCompositionForwardDiff (n + 2) := by
        nlinarith [hmul, hq_pos]
      exact le_trans htmp (forwardDiff_mono hlogconvex (n + 3) (by omega))

private lemma secant_lt_forwardDiff
    (hstrict : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) <
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1)) :
    ∀ n : ℕ,
      pomMultiplicityCompositionLambdaSecantSlope (n + 2) <
        pomMultiplicityCompositionForwardDiff (n + 2)
  | 0 => by
      rw [secant_two_eq]
      simpa using forwardDiff_strict_mono hstrict 2 (by omega)
  | n + 1 => by
      have ih := secant_lt_forwardDiff hstrict n
      have hrec := secant_succ_recurrence (n + 2) (by omega)
      have hq_pos : 0 < ((n + 2 : ℕ) : ℝ) := by positivity
      have hcoeff_pos : 0 < (((n + 2 : ℕ) : ℝ) - 1) := by
        have hgt : (1 : ℝ) < ((n + 2 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 < n + 2 by omega)
        linarith
      have hih :
          (((n + 2 : ℕ) : ℝ) - 1) * pomMultiplicityCompositionLambdaSecantSlope (n + 2) <
            (((n + 2 : ℕ) : ℝ) - 1) * pomMultiplicityCompositionForwardDiff (n + 2) := by
        exact mul_lt_mul_of_pos_left ih hcoeff_pos
      have hmul :
          ((n + 2 : ℕ) : ℝ) * pomMultiplicityCompositionLambdaSecantSlope (n + 3) <
            ((n + 2 : ℕ) : ℝ) * pomMultiplicityCompositionForwardDiff (n + 2) := by
        nlinarith [hrec, hih]
      have htmp : pomMultiplicityCompositionLambdaSecantSlope (n + 3) <
          pomMultiplicityCompositionForwardDiff (n + 2) := by
        nlinarith [hmul, hq_pos]
      exact lt_trans htmp (forwardDiff_strict_mono hstrict (n + 3) (by omega))

private lemma secant_step_mono
    (hlogconvex : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) ≤
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    pomMultiplicityCompositionLambdaSecantSlope q ≤
      pomMultiplicityCompositionLambdaSecantSlope (q + 1) := by
  have hrec := secant_succ_recurrence q hq
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hdiff_raw := secant_le_forwardDiff hlogconvex (q - 2)
  have hdiff : pomMultiplicityCompositionLambdaSecantSlope q ≤
      pomMultiplicityCompositionForwardDiff q := by
    simpa [Nat.sub_add_cancel hq] using hdiff_raw
  have hmul : (q : ℝ) * pomMultiplicityCompositionLambdaSecantSlope q ≤
      (q : ℝ) * pomMultiplicityCompositionLambdaSecantSlope (q + 1) := by
    nlinarith [hrec, hdiff]
  nlinarith [hmul, hq_pos]

private lemma secant_step_strict_mono
    (hstrict : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) <
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    pomMultiplicityCompositionLambdaSecantSlope q <
      pomMultiplicityCompositionLambdaSecantSlope (q + 1) := by
  have hrec := secant_succ_recurrence q hq
  have hq_pos : 0 < (q : ℝ) := by positivity
  have hdiff_raw := secant_lt_forwardDiff hstrict (q - 2)
  have hdiff : pomMultiplicityCompositionLambdaSecantSlope q <
      pomMultiplicityCompositionForwardDiff q := by
    simpa [Nat.sub_add_cancel hq] using hdiff_raw
  have hmul : (q : ℝ) * pomMultiplicityCompositionLambdaSecantSlope q <
      (q : ℝ) * pomMultiplicityCompositionLambdaSecantSlope (q + 1) := by
    nlinarith [hrec, hdiff]
  nlinarith [hmul, hq_pos]

set_option maxHeartbeats 400000 in
/-- Paper label: `prop:pom-multiplicity-composition-logconvex-lambdaq`.
Assuming the moment-hierarchy growth constants satisfy the adjacent log-convexity inequality,
their logarithms form a discrete convex sequence, so the secant slopes from `q = 1` are
monotone. Under the strict version, the induced Rényi entropy-rate profile is strictly
decreasing. -/
theorem paper_pom_multiplicity_composition_logconvex_lambdaq
    (hlogconvex : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) ≤
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (hstrict : ∀ q, 2 ≤ q →
      pomMultiplicityCompositionLambda q ^ (2 : Nat) <
        pomMultiplicityCompositionLambda (q - 1) * pomMultiplicityCompositionLambda (q + 1))
    (q : ℕ) (hq : 2 ≤ q) :
    Real.log (pomMultiplicityCompositionLambda q) -
        (Real.log (pomMultiplicityCompositionLambda (q - 1)) +
            Real.log (pomMultiplicityCompositionLambda (q + 1))) / 2 ≤ 0 ∧
      pomMultiplicityCompositionLambdaSecantSlope q ≤
        pomMultiplicityCompositionLambdaSecantSlope (q + 1) ∧
      pomMultiplicityCompositionRenyiEntropyRate (q + 1) <
        pomMultiplicityCompositionRenyiEntropyRate q := by
  constructor
  · have hlog := logconvex_log_ineq hlogconvex q hq
    linarith
  constructor
  · exact secant_step_mono hlogconvex q hq
  · unfold pomMultiplicityCompositionRenyiEntropyRate
    have hs := secant_step_strict_mono hstrict q hq
    linarith

end

end Omega.POM
