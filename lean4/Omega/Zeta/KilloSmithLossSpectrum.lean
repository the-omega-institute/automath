import Omega.Zeta.SmithEntropyInvertsVpInvariants
import Omega.Zeta.XiSmithLossMinimalBranchRegister

namespace Omega.Zeta

/-- Paper label: `thm:killo-smith-loss-spectrum`. -/
theorem paper_killo_smith_loss_spectrum (p n m : Nat) (smithExponents : Multiset Nat) :
    (∀ k : Nat,
      Omega.Zeta.smithFiberCardinality p n m k smithExponents =
        p ^ (k * (n - m) + Omega.Zeta.smithEntropy smithExponents k)) ∧
    (∀ k : Nat,
      Omega.Zeta.smithEntropy smithExponents (k + 1) -
          Omega.Zeta.smithEntropy smithExponents k =
        Omega.Zeta.smithDelta smithExponents (k + 1)) ∧
    (∀ e : Nat,
      (smithExponents.filter fun v => v = e).card =
        Omega.Zeta.smithDelta smithExponents e -
          Omega.Zeta.smithDelta smithExponents (e + 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro k
    rfl
  · intro k
    rw [smithEntropy_succ_eq_add_delta]
    exact Nat.add_sub_cancel_left _ _
  · intro e
    exact smithMultiplicity_eq_delta_sub smithExponents e

end Omega.Zeta
