import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The Apéry threshold `w_r = 34 * ((13 * r) % 21)` for `⟨21,34⟩`. -/
def xi_window6_gap_ledger_invariants_w (r : Fin 21) : ℕ :=
  34 * ((13 * r.1) % 21)

/-- The gap multiplicity `g_r = (w_r - r) / 21` in residue class `r`. -/
def xi_window6_gap_ledger_invariants_g (r : Fin 21) : ℕ :=
  (xi_window6_gap_ledger_invariants_w r - r.1) / 21

/-- The quadratic ledger term `binom(g_r, 2)`. -/
def xi_window6_gap_ledger_invariants_binom2 (n : ℕ) : ℕ :=
  n * (n - 1) / 2

/-- Total number of unreachable increments. -/
def xi_window6_gap_ledger_invariants_gapCard : ℕ :=
  Finset.univ.sum xi_window6_gap_ledger_invariants_g

/-- Total weight of the unreachable increments, summed residue class by residue class. -/
def xi_window6_gap_ledger_invariants_gapWeight : ℕ :=
  Finset.univ.sum fun r : Fin 21 =>
    r.1 * xi_window6_gap_ledger_invariants_g r +
      21 * xi_window6_gap_ledger_invariants_binom2
        (xi_window6_gap_ledger_invariants_g r)

/-- Paper label: `prop:xi-window6-gap-ledger-invariants`.
The Apéry-threshold gap counts `g_r` satisfy the exact size, first-moment, and second-order ledger
identities for the unreachable increment set of `⟨21,34⟩`, and the shifted dimension mean is
`722 / 3`. -/
theorem paper_xi_window6_gap_ledger_invariants :
    xi_window6_gap_ledger_invariants_gapCard = 330 ∧
      xi_window6_gap_ledger_invariants_gapWeight = 75460 ∧
      (xi_window6_gap_ledger_invariants_gapWeight : ℚ) /
          xi_window6_gap_ledger_invariants_gapCard =
        686 / 3 ∧
      (Finset.univ.sum fun r : Fin 21 =>
          xi_window6_gap_ledger_invariants_binom2
            (xi_window6_gap_ledger_invariants_g r)) =
        3432 ∧
      (Finset.univ.sum fun r : Fin 21 => (xi_window6_gap_ledger_invariants_g r) ^ 2) = 7194 ∧
      (Finset.univ.sum fun r : Fin 21 => r.1 * xi_window6_gap_ledger_invariants_g r) = 3388 ∧
      ((xi_window6_gap_ledger_invariants_gapWeight +
            12 * xi_window6_gap_ledger_invariants_gapCard : ℚ) /
          xi_window6_gap_ledger_invariants_gapCard =
        722 / 3) := by
  native_decide

end Omega.Zeta
