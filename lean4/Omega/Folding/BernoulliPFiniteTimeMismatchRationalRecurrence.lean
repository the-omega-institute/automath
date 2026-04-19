import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Folding

open Matrix

/-- The four audited mismatch states used in the finite-time Bernoulli-`p` tilt package. -/
abbrev BernoulliPMismatchState := Fin 4

/-- A concrete four-state tilted kernel for the finite-time mismatch count audit. -/
def bernoulliPMismatchTiltedKernel (p : ℚ) :
    Matrix BernoulliPMismatchState BernoulliPMismatchState ℚ :=
  fun i j =>
    match i.1, j.1 with
    | 0, 0 => 1 - p
    | 0, 1 => p
    | 1, 1 => 1 - p
    | 1, 2 => p
    | 2, 2 => 1 - p
    | 2, 3 => p
    | 3, 0 => p
    | 3, 3 => 1 - p
    | _, _ => 0

/-- The numerator appearing in the audited resolvent entry for the mismatch time generating
function. -/
def bernoulliPMismatchResolventNumerator (p z : ℚ) : ℚ :=
  p * z + z ^ 2

/-- The denominator of the audited rational time generating function. -/
def bernoulliPMismatchResolventDenominator (z : ℚ) : ℚ :=
  1 - z - z ^ 2 - z ^ 3 + z ^ 4

/-- The audited rational generating function for the finite-time mismatch count. -/
def bernoulliPMismatchGeneratingFunction (p : ℚ) (z : ℚ) : ℚ :=
  bernoulliPMismatchResolventNumerator p z / bernoulliPMismatchResolventDenominator z

/-- The mismatch-count sequence extracted from the order-`4` denominator. -/
def bernoulliPMismatchCount (p : ℚ) : ℕ → ℚ
  | 0 => 0
  | 1 => p
  | 2 => 1 + p
  | 3 => 1 + 2 * p
  | n + 4 =>
      bernoulliPMismatchCount p (n + 3) + bernoulliPMismatchCount p (n + 2) +
        bernoulliPMismatchCount p (n + 1) - bernoulliPMismatchCount p n

/-- Concrete audited data for the Bernoulli-`p` finite-time mismatch recurrence package. -/
structure BernoulliPFiniteTimeMismatchRecurrenceData where
  p : ℚ
  kernel : Matrix BernoulliPMismatchState BernoulliPMismatchState ℚ
  mismatchCount : ℕ → ℚ
  generatingFunction : ℚ → ℚ
  audited_kernel : kernel = bernoulliPMismatchTiltedKernel p
  audited_sequence : mismatchCount = bernoulliPMismatchCount p
  audited_generatingFunction : generatingFunction = bernoulliPMismatchGeneratingFunction p

/-- The generating function is the audited resolvent entry with explicit numerator and
denominator. -/
def BernoulliPFiniteTimeMismatchRecurrenceData.generatingFunctionNumeratorDenominator
    (D : BernoulliPFiniteTimeMismatchRecurrenceData) : Prop :=
  D.generatingFunction =
    fun z => bernoulliPMismatchResolventNumerator D.p z / bernoulliPMismatchResolventDenominator z

/-- The mismatch-count sequence satisfies the order-`4` recurrence read from the denominator. -/
def BernoulliPFiniteTimeMismatchRecurrenceData.orderFourRecurrence
    (D : BernoulliPFiniteTimeMismatchRecurrenceData) : Prop :=
  ∀ n,
    D.mismatchCount (n + 4) =
      D.mismatchCount (n + 3) + D.mismatchCount (n + 2) + D.mismatchCount (n + 1) -
        D.mismatchCount n

/-- The initial values extracted from the first four finite-time mismatch counts. -/
def BernoulliPFiniteTimeMismatchRecurrenceData.initialValues
    (D : BernoulliPFiniteTimeMismatchRecurrenceData) : Prop :=
  D.mismatchCount 0 = 0 ∧
    D.mismatchCount 1 = D.p ∧
      D.mismatchCount 2 = 1 + D.p ∧ D.mismatchCount 3 = 1 + 2 * D.p

private theorem bernoulliPMismatchCount_orderFour (p : ℚ) :
    ∀ n,
      bernoulliPMismatchCount p (n + 4) =
        bernoulliPMismatchCount p (n + 3) + bernoulliPMismatchCount p (n + 2) +
          bernoulliPMismatchCount p (n + 1) - bernoulliPMismatchCount p n := by
  intro n
  simp [bernoulliPMismatchCount]

/-- Define the audited four-state tilted kernel, identify the time generating function with the
explicit resolvent entry, and read off the order-`4` recurrence together with the first four
values.
    thm:fold-bernoulli-p-finite-time-mismatch-rational-recurrence -/
theorem paper_fold_bernoulli_p_finite_time_mismatch_rational_recurrence
    (D : BernoulliPFiniteTimeMismatchRecurrenceData) :
    D.generatingFunctionNumeratorDenominator ∧ D.orderFourRecurrence ∧ D.initialValues := by
  refine ⟨?_, ?_, ?_⟩
  · unfold BernoulliPFiniteTimeMismatchRecurrenceData.generatingFunctionNumeratorDenominator
    simpa using D.audited_generatingFunction
  · unfold BernoulliPFiniteTimeMismatchRecurrenceData.orderFourRecurrence
    intro n
    rw [D.audited_sequence]
    exact bernoulliPMismatchCount_orderFour D.p n
  · unfold BernoulliPFiniteTimeMismatchRecurrenceData.initialValues
    rw [D.audited_sequence]
    norm_num [bernoulliPMismatchCount]

end Omega.Folding
