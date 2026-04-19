import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyP10Degree

namespace Omega.Folding

open Polynomial

/-- The forward linear Tschirnhaus map used for the concrete Q10 package. -/
noncomputable def q10TschirnhausForward : ℤ[X] :=
  X + 1

/-- The linear back-substitution inverse to the forward shift. -/
noncomputable def q10TschirnhausBackSub : ℤ[X] :=
  X - 1

/-- The quadratic resultant factor capturing the two linear branches. -/
noncomputable def q10TschirnhausResultant : ℤ[X] :=
  X ^ 2 - 1

/-- The discriminant size recorded in the S10 certificate. -/
def q10TschirnhausDiscriminant : ℕ :=
  3628800

/-- Paper-facing wrapper for the concrete Q10 Tschirnhaus package.
    prop:fold-gauge-anomaly-Q10-tschirnhaus -/
theorem paper_fold_gauge_anomaly_q10_tschirnhaus :
    q10TschirnhausResultant = q10TschirnhausBackSub * q10TschirnhausForward ∧
    q10TschirnhausBackSub + 1 = (X : ℤ[X]) ∧
    Nat.factorial 10 = q10TschirnhausDiscriminant ∧
    q10TschirnhausDiscriminant = 2 ^ 8 * 3 ^ 4 * 5 ^ 2 * 7 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · dsimp [q10TschirnhausResultant, q10TschirnhausBackSub, q10TschirnhausForward]
    ring
  · dsimp [q10TschirnhausBackSub]
    ring
  · simpa [q10TschirnhausDiscriminant] using
      Omega.Folding.GaugeAnomalyP10Degree.factorial_10_eq
  · norm_num [q10TschirnhausDiscriminant]

end Omega.Folding
