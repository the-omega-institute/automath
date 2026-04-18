import Mathlib.Tactic

namespace Omega.Discussion

/-- The bridge must externalize prime-like information beyond a fixed finite window. -/
def nonlocalPrimeRegisterRequirement (fixedWindowBudget primeRegisterBudget : ℕ) : Prop :=
  fixedWindowBudget < primeRegisterBudget

/-- Visible control only survives once the observation budget dominates the diffusive modulus
scale. -/
def doubleLimitVisibilityRequirement (modulusDepth timeBudget : ℕ) : Prop :=
  modulusDepth ≤ timeBudget

/-- A finite-dimensional determinant model must be upgraded to a genuinely Fredholm-scale object. -/
def fredholmUpgradeRequirement (finiteDeterminantRank fredholmRank : ℕ) : Prop :=
  finiteDeterminantRank < fredholmRank

/-- Concrete discussion wrapper for the three bridge-paradigm no-go inputs.
    thm:bridge-paradigm-nonlocal-doublelimit-fredholm -/
theorem paper_discussion_bridge_paradigm_nonlocal_doublelimit_fredholm
    (fixedWindowBudget primeRegisterBudget modulusDepth timeBudget
      finiteDeterminantRank fredholmRank : ℕ)
    (hPrimeShadow : fixedWindowBudget + 1 ≤ primeRegisterBudget)
    (hDiffusiveSlowMode : modulusDepth * modulusDepth ≤ timeBudget)
    (hFiniteDeterminantRigidity : finiteDeterminantRank + 1 ≤ fredholmRank) :
    nonlocalPrimeRegisterRequirement fixedWindowBudget primeRegisterBudget ∧
      doubleLimitVisibilityRequirement modulusDepth timeBudget ∧
      fredholmUpgradeRequirement finiteDeterminantRank fredholmRank := by
  refine ⟨?_, ?_, ?_⟩
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self fixedWindowBudget) hPrimeShadow
  · exact le_trans (Nat.le_mul_self modulusDepth) hDiffusiveSlowMode
  · exact Nat.lt_of_lt_of_le (Nat.lt_succ_self finiteDeterminantRank) hFiniteDeterminantRigidity

end Omega.Discussion
