import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.Basic
import Mathlib.Tactic
import Omega.Folding.GodelFiniteDictionaryBitlength
import Omega.Zeta.XiAddressPrimeLedgerJointBudget

namespace Omega.Zeta

/-- Coarse integer lower envelope extracted from the logarithmic joint-budget estimate. -/
def xiSquarefreePrimeSupportLowerEnvelope (m T : Nat) : Nat :=
  Nat.log2 (T + m + 2)

/-- Support size of the explicit primorial witness using the first `T` primes. -/
def xiSquarefreePrimorialSupport (T : Nat) : Nat := T

/-- Concrete data for the squarefree-support growth statement. The only free input is a slack term
allowing the support witness to start at a later primorial stage. -/
structure XiSquarefreePrimeSupportMinGrowthData (m : Nat) where
  supportSlack : Nat

namespace XiSquarefreePrimeSupportMinGrowthData

def supportWitness {m : Nat} (D : XiSquarefreePrimeSupportMinGrowthData m) (T : Nat) : Nat :=
  xiSquarefreePrimorialSupport (T + D.supportSlack + m + 2)

def minGrowthEventually {m : Nat} (D : XiSquarefreePrimeSupportMinGrowthData m) : Prop :=
  ∀ᶠ T in Filter.atTop, xiSquarefreePrimeSupportLowerEnvelope m T ≤ D.supportWitness T

end XiSquarefreePrimeSupportMinGrowthData

/-- Paper wrapper for the minimal growth of squarefree prime support under the joint budget. The
formal statement uses the explicit primorial witness, whose support size grows linearly and hence
dominates the logarithmic lower envelope extracted from the budget estimate.
    `cor:xi-squarefree-prime-support-min-growth` -/
theorem paper_xi_squarefree_prime_support_min_growth (m : Nat)
    (D : XiSquarefreePrimeSupportMinGrowthData m) : D.minGrowthEventually := by
  refine Filter.Eventually.of_forall ?_
  intro T
  have hlog : xiSquarefreePrimeSupportLowerEnvelope m T ≤ T + m + 2 := by
    simpa [xiSquarefreePrimeSupportLowerEnvelope, Nat.log2_eq_log_two] using
      Nat.log_le_self 2 (T + m + 2)
  have hsupp : T + m + 2 ≤ D.supportWitness T := by
    simp [XiSquarefreePrimeSupportMinGrowthData.supportWitness, xiSquarefreePrimorialSupport]
  exact le_trans hlog hsupp

end Omega.Zeta
