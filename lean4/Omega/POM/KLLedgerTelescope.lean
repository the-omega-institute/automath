import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Omega.POM.KLPythagorasTower

namespace Omega.POM

open Finset

private theorem paper_pom_kl_ledger_telescope_aux
    (R : ResolutionReflectorData) {M : Nat} (mu : R.Distrib M) :
    ∀ ⦃m : Nat⦄, 1 ≤ m → m ≤ M →
      R.kl (M := M) mu (R.reflect 1 mu) =
        (Finset.Icc 2 m).sum (fun k => R.kl (M := M) (R.reflect k mu) (R.reflect (k - 1) mu)) +
          R.kl (M := M) mu (R.reflect m mu)
  | 1, _, _ => by simp
  | m + 1, hm, hmM => by
      cases m with
      | zero =>
          simp
      | succ m =>
          have hprev :=
            paper_pom_kl_ledger_telescope_aux R mu (Nat.succ_le_succ (Nat.zero_le m))
              (Nat.le_of_succ_le hmM)
          have hstep :
              R.kl (M := M) mu (R.reflect (m + 1) mu) =
                R.kl (M := M) mu (R.reflect (m + 2) mu) +
                  R.kl (M := M) (R.reflect (m + 2) mu) (R.reflect (m + 1) mu) := by
            simpa using
              paper_pom_kl_pythagoras_tower (R := R) (M := M) (m1 := m + 1) (m2 := m + 2)
                hmM (Nat.le_succ (m + 1)) mu
          calc
            R.kl (M := M) mu (R.reflect 1 mu)
                = (Finset.Icc 2 (m + 1)).sum
                    (fun k => R.kl (M := M) (R.reflect k mu) (R.reflect (k - 1) mu)) +
                    R.kl (M := M) mu (R.reflect (m + 1) mu) := hprev
            _ = (Finset.Icc 2 (m + 1)).sum
                  (fun k => R.kl (M := M) (R.reflect k mu) (R.reflect (k - 1) mu)) +
                  (R.kl (M := M) mu (R.reflect (m + 2) mu) +
                    R.kl (M := M) (R.reflect (m + 2) mu) (R.reflect (m + 1) mu)) := by
                    rw [hstep]
            _ = (Finset.Icc 2 (m + 2)).sum
                  (fun k => R.kl (M := M) (R.reflect k mu) (R.reflect (k - 1) mu)) +
                  R.kl (M := M) mu (R.reflect (m + 2) mu) := by
                    have hsub : m + 2 - 1 = m + 1 := by omega
                    rw [Finset.sum_Icc_succ_top (show 2 ≤ m + 2 by omega)]
                    simp [hsub, add_assoc, add_left_comm, add_comm]

/-- The KL tower identity telescopes along the reflector chain: summing the one-step reflected
comparisons from levels `2` through `M` leaves only the endpoint residual at level `M`.
    cor:pom-kl-ledger-telescope -/
theorem paper_pom_kl_ledger_telescope
    (R : ResolutionReflectorData) {M : Nat} (hM : 1 <= M) (mu : R.Distrib M) :
    R.kl (M := M) mu (R.reflect 1 mu) =
      (Finset.Icc 2 M).sum (fun m => R.kl (M := M) (R.reflect m mu) (R.reflect (m - 1) mu)) +
        R.kl (M := M) mu (R.reflect M mu) := by
  exact paper_pom_kl_ledger_telescope_aux R mu hM (le_rfl)

end Omega.POM
