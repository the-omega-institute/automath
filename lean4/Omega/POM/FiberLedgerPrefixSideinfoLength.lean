import Mathlib.Data.Real.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Concrete finite-fiber data for the prefix side-information ledger argument.
`fiberConditionalEntropy x` is the base-`M` conditional entropy contribution from the fiber over
`x`, `fiberUniformLift x` is the matching uniform-lift contribution, and `fiberMeanLength x` is the
average prefix length used on that fiber. -/
structure FiberLedgerPrefixSideinfoData where
  X : Type
  instFintypeX : Fintype X
  instDecidableEqX : DecidableEq X
  weight : X → ℝ
  fiberConditionalEntropy : X → ℝ
  fiberUniformLift : X → ℝ
  fiberMeanLength : X → ℝ
  conditionalEntropy : ℝ
  uniformLiftBudget : ℝ
  expectedLength : ℝ
  klGap : ℝ
  conditionalEntropy_eq_sum :
    conditionalEntropy = ∑ x, weight x * fiberConditionalEntropy x
  uniformLiftBudget_eq_sum :
    uniformLiftBudget = ∑ x, weight x * fiberUniformLift x
  expectedLength_eq_sum :
    expectedLength = ∑ x, weight x * fiberMeanLength x
  localPrefixLower :
    ∀ x, weight x * fiberConditionalEntropy x ≤ weight x * fiberMeanLength x
  localUniformUpper :
    ∀ x, weight x * fiberMeanLength x ≤ weight x * fiberUniformLift x + weight x
  weights_sum_one : (∑ x, weight x) = 1
  ledger_identity : conditionalEntropy = uniformLiftBudget - klGap
  kl_nonneg : 0 ≤ klGap

attribute [instance] FiberLedgerPrefixSideinfoData.instFintypeX
attribute [instance] FiberLedgerPrefixSideinfoData.instDecidableEqX

namespace FiberLedgerPrefixSideinfoData

/-- Prefix-free lower bound chain in base-`M` units:
the expected prefix length dominates the conditional entropy, which equals the uniform-lift budget
minus the KL ledger term, and hence also dominates the budget after subtracting any further
nonnegative slack. -/
def lowerBoundChain (D : FiberLedgerPrefixSideinfoData) : Prop :=
  D.expectedLength ≥ D.conditionalEntropy ∧
    D.conditionalEntropy = D.uniformLiftBudget - D.klGap ∧
    D.uniformLiftBudget - D.klGap ≥ D.conditionalEntropy - D.klGap

/-- In the uniform-lift case (`klGap = 0`), the standard Shannon-style per-fiber construction gives
an average prefix length within `+1` of the fiberwise base-`M` log budget. -/
def uniformLiftUpperBound (D : FiberLedgerPrefixSideinfoData) : Prop :=
  D.klGap = 0 → D.expectedLength ≤ D.uniformLiftBudget + 1

lemma expectedLength_ge_conditionalEntropy (D : FiberLedgerPrefixSideinfoData) :
    D.conditionalEntropy ≤ D.expectedLength := by
  rw [D.conditionalEntropy_eq_sum, D.expectedLength_eq_sum]
  calc
    ∑ x, D.weight x * D.fiberConditionalEntropy x
      ≤ ∑ x, D.weight x * D.fiberMeanLength x := by
        exact Finset.sum_le_sum (fun x _ => D.localPrefixLower x)
    _ = ∑ x, D.weight x * D.fiberMeanLength x := rfl

lemma expectedLength_le_uniformLiftBudget_add_one (D : FiberLedgerPrefixSideinfoData) :
    D.expectedLength ≤ D.uniformLiftBudget + 1 := by
  calc
    D.expectedLength = ∑ x, D.weight x * D.fiberMeanLength x := D.expectedLength_eq_sum
    _ ≤ ∑ x, (D.weight x * D.fiberUniformLift x + D.weight x) := by
        exact Finset.sum_le_sum (fun x _ => D.localUniformUpper x)
    _ = (∑ x, D.weight x * D.fiberUniformLift x) + ∑ x, D.weight x := by
        simp_rw [Finset.sum_add_distrib]
    _ = (∑ x, D.weight x * D.fiberUniformLift x) + 1 := by
        rw [D.weights_sum_one]
    _ = D.uniformLiftBudget + 1 := by
        rw [← D.uniformLiftBudget_eq_sum]

lemma lowerBoundChain_holds (D : FiberLedgerPrefixSideinfoData) : D.lowerBoundChain := by
  refine ⟨D.expectedLength_ge_conditionalEntropy, D.ledger_identity, ?_⟩
  have hle : D.conditionalEntropy - D.klGap ≤ D.conditionalEntropy := by
    linarith [D.kl_nonneg]
  simpa [D.ledger_identity] using hle

lemma uniformLiftUpperBound_holds (D : FiberLedgerPrefixSideinfoData) : D.uniformLiftUpperBound := by
  intro hkl
  simpa [hkl] using D.expectedLength_le_uniformLiftBudget_add_one

end FiberLedgerPrefixSideinfoData

open FiberLedgerPrefixSideinfoData

/-- Fiberwise prefix-free side-information length: the lower-bound chain is obtained by summing the
fiberwise Shannon lower bounds, and the uniform-lift case admits the standard `+1` prefix coding
construction on each fiber.
    thm:pom-fiber-ledger-prefix-sideinfo-length -/
theorem paper_pom_fiber_ledger_prefix_sideinfo_length (D : FiberLedgerPrefixSideinfoData) :
    D.lowerBoundChain ∧ D.uniformLiftUpperBound := by
  exact ⟨D.lowerBoundChain_holds, D.uniformLiftUpperBound_holds⟩

end Omega.POM
