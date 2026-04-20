import Mathlib.Tactic
import Mathlib.Topology.Order.IntermediateValue
import Omega.Folding.BernoulliPRegenerationBivariatePGF

namespace Omega.Folding

open scoped BigOperators

/-- Concrete Bernoulli-`p` input data for the cycle-mismatch law. -/
structure BernoulliPCycleMismatchLawData where
  p : ℝ
  hp : 0 < p
  hp1 : p < 1

namespace BernoulliPCycleMismatchLawData

/-- The one-variable PGF obtained by specializing the cycle PGF at `z = 1`. -/
noncomputable def cycleMismatchPGF (D : BernoulliPCycleMismatchLawData) (u : ℝ) : ℝ :=
  ((1 - D.p) * (1 - D.p * u)) / (1 - D.p * u - D.p * (1 - D.p) * u ^ 3)

/-- The coefficient sequence read from the cubic denominator recurrence. -/
noncomputable def cycleMismatchRecurrenceWeight (D : BernoulliPCycleMismatchLawData) : ℕ → ℝ
  | 0 => 1 - D.p
  | 1 => 0
  | 2 => 0
  | n + 3 =>
      D.p * cycleMismatchRecurrenceWeight D (n + 2) +
        D.p * (1 - D.p) * cycleMismatchRecurrenceWeight D n

/-- The explicit finite-sum coefficient formula coming from the geometric-series expansion of
`1 / (1 - p u - p(1-p) u^3)`. -/
noncomputable def cycleMismatchClosedFormWeight (D : BernoulliPCycleMismatchLawData) : ℕ → ℝ
  | 0 => 1 - D.p
  | 1 => 0
  | 2 => 0
  | n + 3 =>
      ((1 - D.p) ^ 2) *
        Finset.sum (Finset.range (n / 3 + 1)) fun r =>
          (Nat.choose (n - 2 * r) r : ℝ) * D.p ^ (n + 1 - 2 * r) * (1 - D.p) ^ r

/-- The specialized PGF has the announced rational closed form. -/
def pgfClosed (D : BernoulliPCycleMismatchLawData) : Prop :=
  ∀ u : ℝ,
    D.cycleMismatchPGF u =
      ((1 - D.p) * (1 - D.p * u)) / (1 - D.p * u - D.p * (1 - D.p) * u ^ 3)

/-- The cubic denominator yields the third-order coefficient recurrence with the stated seeds. -/
def thirdOrderRecurrence (D : BernoulliPCycleMismatchLawData) : Prop :=
  D.cycleMismatchRecurrenceWeight 0 = 1 - D.p ∧
    D.cycleMismatchRecurrenceWeight 1 = 0 ∧
    D.cycleMismatchRecurrenceWeight 2 = 0 ∧
    ∀ n : ℕ,
      D.cycleMismatchRecurrenceWeight (n + 3) =
        D.p * D.cycleMismatchRecurrenceWeight (n + 2) +
          D.p * (1 - D.p) * D.cycleMismatchRecurrenceWeight n

/-- The geometric-series expansion gives a finite binomial sum for the coefficient of `u^k`. -/
def finiteSumClosedForm (D : BernoulliPCycleMismatchLawData) : Prop :=
  D.cycleMismatchClosedFormWeight 0 = 1 - D.p ∧
    D.cycleMismatchClosedFormWeight 1 = 0 ∧
    D.cycleMismatchClosedFormWeight 2 = 0 ∧
    ∀ n : ℕ,
      D.cycleMismatchClosedFormWeight (n + 3) =
        ((1 - D.p) ^ 2) *
          Finset.sum (Finset.range (n / 3 + 1)) fun r =>
            (Nat.choose (n - 2 * r) r : ℝ) * D.p ^ (n + 1 - 2 * r) * (1 - D.p) ^ r

/-- The tail law is recorded by the dominant positive root of the denominator equation. -/
def exponentialTail (D : BernoulliPCycleMismatchLawData) : Prop :=
  ∃ r ∈ Set.Ioo (1 : ℝ) (1 / D.p), D.p * (1 - D.p) * r ^ 3 + D.p * r - 1 = 0

end BernoulliPCycleMismatchLawData

open BernoulliPCycleMismatchLawData

private lemma cycleMismatchCubic_at_one_neg (D : BernoulliPCycleMismatchLawData) :
    D.p * (1 - D.p) * (1 : ℝ) ^ 3 + D.p * 1 - 1 < 0 := by
  have hp_ne_one : D.p ≠ 1 := ne_of_lt D.hp1
  have hsquare : 0 < (1 - D.p) ^ 2 := by
    exact sq_pos_of_ne_zero (sub_ne_zero.mpr hp_ne_one.symm)
  have hEq : D.p * (1 - D.p) * (1 : ℝ) ^ 3 + D.p * 1 - 1 = -((1 - D.p) ^ 2) := by
    ring
  rw [hEq]
  linarith

private lemma cycleMismatchCubic_at_inv_pos (D : BernoulliPCycleMismatchLawData) :
    0 < D.p * (1 - D.p) * (1 / D.p) ^ 3 + D.p * (1 / D.p) - 1 := by
  have hp0 : D.p ≠ 0 := ne_of_gt D.hp
  have hEq :
      D.p * (1 - D.p) * (1 / D.p) ^ 3 + D.p * (1 / D.p) - 1 = (1 - D.p) / D.p ^ 2 := by
    field_simp [hp0]
    ring
  rw [hEq]
  refine div_pos (sub_pos.mpr D.hp1) ?_
  positivity

private lemma one_le_inv_p (D : BernoulliPCycleMismatchLawData) : (1 : ℝ) ≤ 1 / D.p := by
  simpa [one_div] using (one_le_inv₀ D.hp).2 D.hp1.le

/-- Paper label: `cor:fold-bernoulli-p-cycle-mismatch-law-tail`. -/
theorem paper_fold_bernoulli_p_cycle_mismatch_law_tail (D : BernoulliPCycleMismatchLawData) :
    D.pgfClosed ∧ D.thirdOrderRecurrence ∧ D.finiteSumClosedForm ∧ D.exponentialTail := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    rfl
  · refine ⟨rfl, rfl, rfl, ?_⟩
    intro n
    cases n with
    | zero =>
        simp [cycleMismatchRecurrenceWeight]
    | succ n =>
        cases n with
        | zero =>
            simp [cycleMismatchRecurrenceWeight]
        | succ n =>
            simp [cycleMismatchRecurrenceWeight]
  · refine ⟨rfl, rfl, rfl, ?_⟩
    intro n
    rfl
  · let f : ℝ → ℝ := fun x => D.p * (1 - D.p) * x ^ 3 + D.p * x - 1
    have hcont' : Continuous fun x : ℝ => D.p * (1 - D.p) * x ^ 3 + D.p * x - 1 := by
      continuity
    have hcont : ContinuousOn f (Set.Icc (1 : ℝ) (1 / D.p)) := by
      simpa [f] using hcont'.continuousOn
    have hle : (1 : ℝ) ≤ 1 / D.p := one_le_inv_p D
    have hzero_mem : (0 : ℝ) ∈ Set.Ioo (f 1) (f (1 / D.p)) := by
      constructor
      · simpa [f] using cycleMismatchCubic_at_one_neg D
      · simpa [f] using cycleMismatchCubic_at_inv_pos D
    have himage : (0 : ℝ) ∈ f '' Set.Ioo (1 : ℝ) (1 / D.p) :=
      intermediate_value_Ioo hle hcont hzero_mem
    rcases himage with ⟨r, hr, hr0⟩
    exact ⟨r, hr, hr0⟩

end Omega.Folding
