import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part50dc-atomic-periodic-residue-cyclotomic-shell`. -/
theorem paper_xi_time_part50dc_atomic_periodic_residue_cyclotomic_shell (m r : ℕ)
    (hm : 0 < m) :
    (let ell := if r % m = 0 then 2 * m else 2 * (r % m);
      0 < ell ∧ ell ≤ 2 * m ∧
        ∀ q : ℕ, 2 * ((if r % m = 0 then m else r % m) + q * m) =
          ell + q * (2 * m)) := by
  by_cases h : r % m = 0
  · simp [h]
    refine ⟨hm, ?_⟩
    intro q
    ring
  · have hpos : 0 < r % m := Nat.pos_of_ne_zero h
    have hlt : r % m < m := Nat.mod_lt r hm
    simp [h]
    refine ⟨by omega, by omega, ?_⟩
    intro q
    ring

end Omega.Zeta
