import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-! ### Nat-level scaffolding for the window-6 visible/hidden separation. -/

/-- `|X_6| = F_8 = 21`.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem fib_eight : Nat.fib 8 = 21 := by decide

/-- `21 = 3 · 7` — the CRT factorization of the window-6 cardinality.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem twentyone_eq_three_times_seven : (21 : Nat) = 3 * 7 := by decide

/-- `gcd(3, 7) = 1` — the CRT coprimality.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem three_seven_coprime : Nat.Coprime 3 7 := by decide

/-! ### ZMod 21 idempotent / orthogonality scaffolding. -/

/-- 7² ≡ 7 (mod 21): `7` is the idempotent of the factor `7`.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem seven_squared_eq_seven_zmod21 : (7 : ZMod 21) * 7 = 7 := by decide

/-- 15² ≡ 15 (mod 21): `15` is the idempotent of the factor `3`.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem fifteen_squared_eq_fifteen_zmod21 : (15 : ZMod 21) * 15 = 15 := by decide

/-- 7 + 15 ≡ 1 (mod 21): the idempotents sum to the identity.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem seven_plus_fifteen_eq_one_zmod21 : (7 : ZMod 21) + 15 = 1 := by decide

/-- 7 · 15 ≡ 0 (mod 21): the idempotents are orthogonal.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem seven_times_fifteen_eq_zero_zmod21 : (7 : ZMod 21) * 15 = 0 := by decide

/-- Additive-hom rigidity at window-6 cardinality: any ZMod-21 additive
    endomorphism fixing 1 is the identity.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem zmod21_add_hom_fixing_one_eq_id
    (σ : ZMod 21 →+ ZMod 21) (h1 : σ 1 = 1) :
    σ = AddMonoidHom.id _ := by
  ext x
  rw [show x = (x.val : ZMod 21) from (ZMod.natCast_zmod_val x).symm]
  rw [← nsmul_one x.val, σ.map_nsmul, h1]
  rfl

/-- Paper package: window-6 visible/hidden separation CRT-idempotent scaffolding.
    thm:conclusion-window6-visible-arithmetic-hidden-parity-absolute-internality -/
theorem paper_window6_visible_hidden_separation :
    Nat.fib 8 = 21 ∧
    (21 : Nat) = 3 * 7 ∧
    Nat.Coprime 3 7 ∧
    (7 : ZMod 21) * 7 = 7 ∧
    (15 : ZMod 21) * 15 = 15 ∧
    (7 : ZMod 21) + 15 = 1 ∧
    (7 : ZMod 21) * 15 = 0 ∧
    (∀ σ : ZMod 21 →+ ZMod 21, σ 1 = 1 → σ = AddMonoidHom.id _) :=
  ⟨fib_eight, twentyone_eq_three_times_seven, three_seven_coprime,
   seven_squared_eq_seven_zmod21, fifteen_squared_eq_fifteen_zmod21,
   seven_plus_fifteen_eq_one_zmod21, seven_times_fifteen_eq_zero_zmod21,
   zmod21_add_hom_fixing_one_eq_id⟩

end Omega.Conclusion
