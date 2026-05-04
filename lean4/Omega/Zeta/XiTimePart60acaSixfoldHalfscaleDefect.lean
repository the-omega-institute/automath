import Mathlib.Tactic
import Omega.Folding.ShiftDynamics

namespace Omega.Zeta

/-- Zeta-facing Lucas denominator for the halfscale defect statement. -/
abbrev xi_time_part60aca_sixfold_halfscale_defect_lucas_num (d : ℕ) : ℕ :=
  if d = 0 then 0 else Omega.lucasNum d

/-- Paper label: `thm:xi-time-part60aca-sixfold-halfscale-defect`. -/
theorem paper_xi_time_part60aca_sixfold_halfscale_defect
    (d : ℕ) (collisionGap klGap : ℚ)
    (hcollision : ((Nat.fib d : ℚ) / Nat.fib (2 * d)) ≤ collisionGap)
    (hkl : (1 / (Omega.Zeta.xi_time_part60aca_sixfold_halfscale_defect_lucas_num d : ℚ)) ≤
      klGap) :
    (1 / (Omega.Zeta.xi_time_part60aca_sixfold_halfscale_defect_lucas_num d : ℚ)) ≤
      collisionGap ∧
      (1 / (Omega.Zeta.xi_time_part60aca_sixfold_halfscale_defect_lucas_num d : ℚ)) ≤
        klGap := by
  constructor
  · by_cases hd : d = 0
    · subst d
      simpa [xi_time_part60aca_sixfold_halfscale_defect_lucas_num] using hcollision
    · have hdpos : 1 ≤ d := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hd)
      have hfib_ne : (Nat.fib d : ℚ) ≠ 0 := by
        exact_mod_cast (Nat.fib_pos.mpr hdpos).ne'
      have hlucas_id : xi_time_part60aca_sixfold_halfscale_defect_lucas_num d =
          Omega.lucasNum d := by
        simp [xi_time_part60aca_sixfold_halfscale_defect_lucas_num, hd]
      have hden : (Nat.fib (2 * d) : ℚ) =
          (Nat.fib d : ℚ) * (xi_time_part60aca_sixfold_halfscale_defect_lucas_num d : ℚ) := by
        rw [hlucas_id]
        exact_mod_cast Omega.fib_double_eq_mul_lucas d
      have hratio : (Nat.fib d : ℚ) / Nat.fib (2 * d) =
          1 / (xi_time_part60aca_sixfold_halfscale_defect_lucas_num d : ℚ) := by
        rw [hden]
        field_simp [hfib_ne]
      rwa [← hratio]
  · exact hkl

end Omega.Zeta
