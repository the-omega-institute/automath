import Mathlib.Data.Fintype.Card
import Omega.SPG.DyadicFiniteMomentCompleteness
import Omega.SPG.ProuhetThueMorsePowerSum

namespace Omega.SPG

open Omega.SPG.ProuhetThueMorsePowerSum

/-- Paper-facing package for the linear-moment holography threshold.
    The first clause is the finite-cardinality lower bound for any injective
    linear readout on a `2^(m*n)`-state dyadic space; the second clause records
    sharpness via the dyadic moment box; the remaining clauses reuse the
    Prouhet--Thue--Morse obstruction package as concrete low-order witnesses.
    thm:spg-linear-moment-holography-minimal-dimension -/
theorem paper_spg_linear_moment_holography_minimal_dim
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L ∧
    Function.Injective (dyadicMomentBox (m := m) (n := n)) ∧
    (∑ j ∈ Finset.range 2, tau j * (j : ℤ) ^ 0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ) ^ 0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ) ^ 1 = 0) := by
  refine ⟨?_, paper_spg_dyadic_finite_moment_completeness, ptm_power_sum_m1_l0,
    ptm_power_sum_m2_l0, ptm_power_sum_m2_l1⟩
  simpa [Fintype.card_fin] using Fintype.card_le_of_injective f hf

/-- Exact paper-facing wrapper for the linear-moment holography threshold package.
    thm:spg-linear-moment-holography-minimal-dimension -/
theorem paper_spg_linear_moment_holography_minimal_dimension
    (m n L : Nat) (f : Fin (2 ^ (m * n)) → Fin L) (hf : Function.Injective f) :
    2 ^ (m * n) ≤ L ∧
    Function.Injective (dyadicMomentBox (m := m) (n := n)) ∧
    (∑ j ∈ Finset.range 2, tau j * (j : ℤ) ^ 0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ) ^ 0 = 0) ∧
    (∑ j ∈ Finset.range 4, tau j * (j : ℤ) ^ 1 = 0) := by
  exact paper_spg_linear_moment_holography_minimal_dim m n L f hf

end Omega.SPG
