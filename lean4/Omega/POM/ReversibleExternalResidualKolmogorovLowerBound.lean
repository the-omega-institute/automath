import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Finite-fiber data for the reversible external residual Kolmogorov lower bound. On each fiber,
the injective residual map gives at least `2^k` residual states, while the Kraft-style short-code
audit bounds the same fiber by at most `2^r`; averaging the resulting fiberwise inequality with a
probability weight gives the expected lower bound. -/
structure ReversibleExternalResidualKolmogorovData where
  Y : Type
  instFintypeY : Fintype Y
  instDecidableEqY : DecidableEq Y
  fiberWeight : Y → ℝ
  fiberCardinality : Y → ℕ
  residualBitLower : Y → ℕ
  descriptionBudget : ℕ
  expectedResidualLower : ℝ
  injectiveResidualAudit : ∀ y, 2 ^ descriptionBudget ≤ fiberCardinality y
  kraftCountingAudit : ∀ y, fiberCardinality y ≤ 2 ^ residualBitLower y
  weight_nonneg : ∀ y, 0 ≤ fiberWeight y
  weights_sum_one : (∑ y, fiberWeight y) = 1
  expectedResidualLower_eq_sum :
    expectedResidualLower = ∑ y, fiberWeight y * (residualBitLower y : ℝ)

attribute [instance] ReversibleExternalResidualKolmogorovData.instFintypeY
attribute [instance] ReversibleExternalResidualKolmogorovData.instDecidableEqY

namespace ReversibleExternalResidualKolmogorovData

/-- The fiberwise lower bound coming from the comparison `2^k ≤ |fiber| ≤ 2^r`. -/
def typicalLowerBound (D : ReversibleExternalResidualKolmogorovData) : Prop :=
  ∀ y, D.descriptionBudget ≤ D.residualBitLower y

/-- The expectation of the residual complexity dominates the short-description budget. -/
def expectedLowerBound (D : ReversibleExternalResidualKolmogorovData) : Prop :=
  (D.descriptionBudget : ℝ) ≤ D.expectedResidualLower

lemma fiberwise_lower_bound (D : ReversibleExternalResidualKolmogorovData) (y : D.Y) :
    D.descriptionBudget ≤ D.residualBitLower y := by
  have hpow : 2 ^ D.descriptionBudget ≤ 2 ^ D.residualBitLower y := by
    exact le_trans (D.injectiveResidualAudit y) (D.kraftCountingAudit y)
  exact (Nat.pow_le_pow_iff_right Nat.one_lt_two).mp hpow

lemma weighted_fiberwise_lower (D : ReversibleExternalResidualKolmogorovData) (y : D.Y) :
    D.fiberWeight y * (D.descriptionBudget : ℝ) ≤
      D.fiberWeight y * (D.residualBitLower y : ℝ) := by
  have hw : 0 ≤ D.fiberWeight y := D.weight_nonneg y
  have hlocal : (D.descriptionBudget : ℝ) ≤ (D.residualBitLower y : ℝ) := by
    exact_mod_cast D.fiberwise_lower_bound y
  nlinarith

lemma typicalLowerBound_holds (D : ReversibleExternalResidualKolmogorovData) :
    D.typicalLowerBound := by
  intro y
  exact D.fiberwise_lower_bound y

lemma expectedLowerBound_holds (D : ReversibleExternalResidualKolmogorovData) :
    D.expectedLowerBound := by
  calc
    (D.descriptionBudget : ℝ) = (∑ y, D.fiberWeight y) * (D.descriptionBudget : ℝ) := by
      rw [D.weights_sum_one, one_mul]
    _ = ∑ y, D.fiberWeight y * (D.descriptionBudget : ℝ) := by
      symm
      rw [Finset.sum_mul]
    _ ≤ ∑ y, D.fiberWeight y * (D.residualBitLower y : ℝ) := by
      exact Finset.sum_le_sum (fun y _ => D.weighted_fiberwise_lower y)
    _ = D.expectedResidualLower := by
      symm
      exact D.expectedResidualLower_eq_sum

end ReversibleExternalResidualKolmogorovData

open ReversibleExternalResidualKolmogorovData

/-- Paper-facing lower bound package: the fiberwise injective residual map and the Kraft counting
audit force the conditional lower bound on every fiber, and averaging those fiberwise inequalities
gives the expected lower bound. -/
theorem paper_pom_reversible_external_residual_kolmogorov_lower_bound
    (D : ReversibleExternalResidualKolmogorovData) :
    D.typicalLowerBound ∧ D.expectedLowerBound := by
  exact ⟨D.typicalLowerBound_holds, D.expectedLowerBound_holds⟩

end Omega.POM
