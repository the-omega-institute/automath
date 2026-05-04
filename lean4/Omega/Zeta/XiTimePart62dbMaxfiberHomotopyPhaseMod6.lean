import Mathlib.Tactic

namespace Omega.Zeta

theorem paper_xi_time_part62db_maxfiber_homotopy_phase_mod6 (F D Dtilde : Nat → Nat)
    (maxNoncontractibleFiber : Nat → Prop)
    (hgap : ∀ m, 17 ≤ m →
      (D m = Dtilde m ↔ m % 6 = 0 ∨ m % 6 = 4) ∧
      (m % 6 = 1 ∨ m % 6 = 5 → D m - Dtilde m = F ((m - 9) / 2)) ∧
      (m % 6 = 2 → D m - Dtilde m = F (m / 2 - 3)) ∧
      (m % 6 = 3 →
        D m - Dtilde m = F ((m - 9) / 2) + F ((m - 17) / 2)))
    (hmax : ∀ m, 17 ≤ m → (maxNoncontractibleFiber m ↔ D m = Dtilde m)) :
    ∀ m, 17 ≤ m → (maxNoncontractibleFiber m ↔ m % 6 = 0 ∨ m % 6 = 4) := by
  intro m hm
  exact (hmax m hm).trans (hgap m hm).1

end Omega.Zeta
