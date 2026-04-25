import Mathlib.Data.Nat.ModEq
import Mathlib.Tactic

namespace Omega.Zeta

/-- The residue map `r ↦ (13 * r) % 21` is an involution on the range `0, ..., 20` because
`13^2 ≡ 1 (mod 21)`.
    prop:xi-window6-congruence-involution -/
theorem paper_xi_window6_congruence_involution (r : Nat) (hr : r < 21) :
    (13 * ((13 * r) % 21)) % 21 = r := by
  have hmod₁ : 13 * ((13 * r) % 21) ≡ 13 * (13 * r) [MOD 21] := by
    exact (Nat.mod_modEq (13 * r) 21).mul_left 13
  have h13 : 13 * 13 ≡ 1 [MOD 21] := by
    native_decide
  have hmod₂ : 13 * (13 * r) ≡ r [MOD 21] := by
    rw [← Nat.mul_assoc]
    exact (h13.mul_right r).trans (by simpa using (Nat.ModEq.refl r))
  exact Nat.mod_eq_of_modEq (hmod₁.trans hmod₂) hr

end Omega.Zeta
