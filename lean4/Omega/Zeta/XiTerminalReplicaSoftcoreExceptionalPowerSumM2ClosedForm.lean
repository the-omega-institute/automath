import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- The two mixed binomial terms in the `m = 2` exceptional power-sum expansion. -/
def xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix (q : Nat) : ℚ :=
  Finset.sum (Finset.range (q + 1)) fun l => (Nat.choose q l : ℚ) * (2 : ℚ) ^ (q - l)

/-- The Fibonacci antidiagonal term coming from the remaining mixed channel in the `m = 2`
decomposition. -/
def xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib (q : Nat) : ℚ :=
  Finset.sum (Finset.antidiagonal (2 * q + 1)) fun p => (Nat.choose p.1 p.2 : ℚ)

/-- The `m = 2` exceptional power sum written in the four-term split from the paper. -/
def xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 (q : Nat) : ℚ :=
  (((4 : ℚ) ^ q) +
      xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
      xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
      xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib q) / 4

/-- Paper label: `cor:xi-terminal-replica-softcore-exceptional-power-sum-m2-closed-form`. The
four-term `m = 2` split collapses to the two binomial contributions `3^q`, `3^q` and the
Fibonacci antidiagonal sum `F_{2q+2}`. -/
theorem paper_xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form (q : Nat) :
    4 * xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q =
      4 ^ q + 2 * 3 ^ q + Nat.fib (2 * q + 2) := by
  have hmix :
      xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q = 3 ^ q := by
    have hpow :
        xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q =
          (1 + 2 : ℚ) ^ q := by
      simpa [xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix,
        mul_comm, mul_left_comm, mul_assoc] using
        (add_pow (1 : ℚ) 2 q).symm
    have hthree : (1 + 2 : ℚ) = 3 := by norm_num
    simpa [hthree] using hpow
  have hfib :
      xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib q =
        Nat.fib (2 * q + 2) := by
    simpa [xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib] using
      (congrArg (fun n : Nat => (n : ℚ)) (Nat.fib_succ_eq_sum_choose (2 * q + 1))).symm
  calc
    4 * xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q
        = 4 *
            ((((4 : ℚ) ^ q) +
                xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
                xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
                xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib q) / 4) := by
              simp [xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2]
    _ = (4 : ℚ) ^ q +
          xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
          xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tmix q +
          xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_Tfib q := by
            field_simp [xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2]
    _ = (4 : ℚ) ^ q + 3 ^ q + 3 ^ q + Nat.fib (2 * q + 2) := by rw [hmix, hfib]
    _ = (4 : ℚ) ^ q + 2 * 3 ^ q + Nat.fib (2 * q + 2) := by ring

/-- Paper label:
`cor:xi-replica-softcore-exceptional-power-sum-square-closed-form-via-fib-necklace`. -/
theorem paper_xi_replica_softcore_exceptional_power_sum_square_closed_form_via_fib_necklace
    (q : Nat) (hq : 2 <= q) :
    4 * xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form_S2 q =
      4 ^ q + 2 * 3 ^ q + Nat.fib (2 * q + 2) := by
  have _hq : 2 <= q := hq
  exact paper_xi_terminal_replica_softcore_exceptional_power_sum_m2_closed_form q

end Omega.Zeta
