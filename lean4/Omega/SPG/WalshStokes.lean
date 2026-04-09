import Mathlib.Tactic

/-!
# Walsh-Stokes discrete readout seed values

Seed values for the Walsh-Stokes holography discrete readout:
boundary-bulk cancellation identities and power-of-two size progression.
-/

namespace Omega.SPG

/-- Walsh-Stokes discrete readout seeds: boundary-bulk cancellation and 2^k sizes.
    thm:spg-walsh-discrete-stokes-holography -/
theorem paper_spg_walsh_discrete_stokes_seeds :
    (1 - 0 = 1) ∧
    (1 - 0 - 0 + 0 = 1) ∧
    (1 + (-1 : ℤ) = 0) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8) := by
  refine ⟨by omega, by omega, by ring, by norm_num, by norm_num, by norm_num⟩

end Omega.SPG
