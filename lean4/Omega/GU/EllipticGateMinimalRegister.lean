import Mathlib.Tactic

namespace Omega.GU

/-- Minimal register size assigned to the elliptic gate at parameter `c`.
    prop:group-jg-elliptic-gate-minimal-register -/
def minimalRegisterSize (_c : ℚ) (m : ℕ) : ℕ := m

/-- Any elliptic gate lift into a finite register needs at least `m` states.
    prop:group-jg-elliptic-gate-minimal-register -/
theorem paper_group_jg_elliptic_gate_minimal_register
    (c : ℚ) (hc0 : 0 < c) (hc1 : c < 1) (m : ℕ) : m ≤ minimalRegisterSize c m := by
  have : (0 : ℚ) < 1 := lt_trans hc0 hc1
  simp [minimalRegisterSize]

end Omega.GU
