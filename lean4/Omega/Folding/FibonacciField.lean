import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Field.ZMod
import Omega.Folding.FiberArithmetic

namespace Omega

/-- cor:field-phase-fib-prime-3 -/
theorem fib_four_prime : Nat.Prime (Nat.fib 4) := by native_decide
/-- cor:field-phase-fib-prime-4 -/
theorem fib_five_prime : Nat.Prime (Nat.fib 5) := by native_decide
/-- cor:field-phase-fib-prime-6 -/
theorem fib_seven_prime : Nat.Prime (Nat.fib 7) := by native_decide
/-- cor:field-phase-fib-prime-8-neg -/
theorem fib_nine_not_prime : ¬ Nat.Prime (Nat.fib 9) := by native_decide
/-- cor:field-phase-fib-prime-12 -/
theorem fib_thirteen_prime : Nat.Prime (Nat.fib 13) := by native_decide

namespace X

noncomputable section

/-- When F(m+2) is prime, every nonzero element has a multiplicative inverse.
    cor:field-phase-fib-prime-inv -/
theorem stableMul_inv_of_prime (hp : Nat.Prime (Nat.fib (m + 2))) (x : X m)
    (hx : x ≠ stableZero) :
    ∃ y : X m, stableMul x y = stableOne := by
  have hP : 1 < Nat.fib (m + 2) := hp.one_lt
  have hne : NeZero (Nat.fib (m + 2)) := ⟨by omega⟩
  have hsv_ne : stableValue x ≠ 0 := fun h =>
    hx ((X.ofNat_stableValue x).symm.trans (by rw [h]; rfl))
  have hsv_lt := stableValue_lt_fib x
  have hcop : Nat.Coprime (stableValue x) (Nat.fib (m + 2)) :=
    (hp.coprime_iff_not_dvd.mpr (Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hsv_ne) hsv_lt)).symm
  -- In ZMod p, stableValue x is a unit with inverse (sv : ZMod p)⁻¹
  have hUnit := (ZMod.isUnit_iff_coprime (stableValue x) (Nat.fib (m + 2))).mpr hcop
  -- Take k = ((sv : ZMod p)⁻¹).val
  set p := Nat.fib (m + 2)
  set sv_zmod := (stableValue x : ZMod p)
  set k := (sv_zmod⁻¹).val
  use X.ofNat m k
  -- Prove via stableValue injectivity
  apply (Function.HasLeftInverse.injective ⟨X.ofNat m, X.ofNat_stableValue⟩)
  simp only [ stableValue_stableMul, stableValue_stableOne hP,
    stableValue_ofNat_lt k (ZMod.val_lt _)]
  -- Goal: (stableValue x * k) % p = 1
  -- From ZMod: sv_zmod * sv_zmod⁻¹ = 1, taking .val gives the mod equation
  have hsv_ne_zmod : sv_zmod ≠ 0 := by
    simp only [sv_zmod, ne_eq, ZMod.natCast_eq_zero_iff]
    exact Nat.not_dvd_of_pos_of_lt (Nat.pos_of_ne_zero hsv_ne) hsv_lt
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hmul_zmod : sv_zmod * sv_zmod⁻¹ = 1 := mul_inv_cancel₀ hsv_ne_zmod
  have hmul : (sv_zmod * sv_zmod⁻¹).val = (1 : ZMod p).val := congr_arg ZMod.val hmul_zmod
  rw [ZMod.val_one] at hmul
  simp only [ZMod.val_mul] at hmul
  -- hmul : sv_zmod.val * sv_zmod⁻¹.val % p = 1
  -- Goal : stableValue x * k % Nat.fib (m + 2) = 1
  -- sv_zmod.val = (stableValue x : ZMod p).val = stableValue x (by val_natCast_of_lt)
  -- k = sv_zmod⁻¹.val (by definition)
  -- p = Nat.fib (m + 2) (by definition)
  rw [show sv_zmod.val = stableValue x from ZMod.val_natCast_of_lt (by omega)] at hmul
  exact hmul

end

end X

end Omega

-- Outside namespace for primality, then re-open for field package
namespace Omega

/-- F(11) = 89 is prime.
    cor:field-phase-fib-prime -/
theorem fib_eleven_prime : Nat.Prime (Nat.fib 11) := by native_decide

/-- F(17) = 1597 is prime.
    cor:field-phase-fib-prime -/
theorem fib_seventeen_prime : Nat.Prime (Nat.fib 17) := by native_decide

/-- Extended field-phase package: X 9 and X 15 are fields (F(11), F(17) prime).
    cor:field-phase-fib-prime -/
theorem paper_fibonacci_field_phase_extended :
    Nat.Prime (Nat.fib 11) ∧ Nat.Prime (Nat.fib 17) ∧
    (∀ x : X 9, x ≠ X.stableZero → ∃ y : X 9, X.stableMul x y = X.stableOne) ∧
    (∀ x : X 15, x ≠ X.stableZero → ∃ y : X 15, X.stableMul x y = X.stableOne) :=
  ⟨fib_eleven_prime, fib_seventeen_prime,
   X.stableMul_inv_of_prime fib_eleven_prime,
   X.stableMul_inv_of_prime fib_seventeen_prime⟩

/-- F(23) = 28657 is prime.
    cor:field-phase-fib-prime -/
theorem fib_twentythree_prime : Nat.Prime (Nat.fib 23) := by native_decide

/-- F(29) = 514229 is prime.
    cor:field-phase-fib-prime -/
theorem fib_twentynine_prime : Nat.Prime (Nat.fib 29) := by native_decide

/-- Extended field-phase package 2: X 21 and X 27 are fields (F(23), F(29) prime).
    cor:field-phase-fib-prime -/
theorem paper_fibonacci_field_phase_extended_2 :
    Nat.Prime (Nat.fib 23) ∧ Nat.Prime (Nat.fib 29) ∧
    (∀ x : X 21, x ≠ X.stableZero → ∃ y : X 21, X.stableMul x y = X.stableOne) ∧
    (∀ x : X 27, x ≠ X.stableZero → ∃ y : X 27, X.stableMul x y = X.stableOne) :=
  ⟨fib_twentythree_prime, fib_twentynine_prime,
   X.stableMul_inv_of_prime fib_twentythree_prime,
   X.stableMul_inv_of_prime fib_twentynine_prime⟩

/-- F(43) = 433494437 is prime.
    cor:field-phase-fib-prime -/
theorem fib_fortythree_prime : Nat.Prime (Nat.fib 43) := by native_decide

/-- Field-phase at m=41: X 41 is a field (F(43) prime).
    cor:field-phase-fib-prime -/
theorem paper_fibonacci_field_phase_m41 :
    Nat.Prime (Nat.fib 43) ∧
    (∀ x : X 41, x ≠ X.stableZero → ∃ y : X 41, X.stableMul x y = X.stableOne) :=
  ⟨fib_fortythree_prime, X.stableMul_inv_of_prime fib_fortythree_prime⟩

/-- Composite: F_15 is not prime.
    cor:field-phase-fib-prime -/
theorem fib_fifteen_not_prime : ¬ Nat.Prime (Nat.fib 15) := by native_decide

/-- Composite: F_19 is not prime.
    cor:field-phase-fib-prime -/
theorem fib_nineteen_not_prime : ¬ Nat.Prime (Nat.fib 19) := by native_decide

/-- Composite: F_21 is not prime.
    cor:field-phase-fib-prime -/
theorem fib_twentyone_not_prime : ¬ Nat.Prime (Nat.fib 21) := by native_decide

/-- Complete Fibonacci prime/composite classification for indices 4..29.
    cor:field-phase-fib-prime -/
theorem paper_fibonacci_prime_composite_classification_1_to_29 :
    Nat.Prime (Nat.fib 4) ∧ Nat.Prime (Nat.fib 5) ∧
    Nat.Prime (Nat.fib 7) ∧ Nat.Prime (Nat.fib 11) ∧
    Nat.Prime (Nat.fib 13) ∧ Nat.Prime (Nat.fib 17) ∧
    Nat.Prime (Nat.fib 23) ∧ Nat.Prime (Nat.fib 29) ∧
    ¬ Nat.Prime (Nat.fib 9) ∧
    ¬ Nat.Prime (Nat.fib 15) ∧
    ¬ Nat.Prime (Nat.fib 19) ∧
    ¬ Nat.Prime (Nat.fib 21) :=
  ⟨fib_four_prime, fib_five_prime, fib_seven_prime, fib_eleven_prime,
   fib_thirteen_prime, fib_seventeen_prime, fib_twentythree_prime, fib_twentynine_prime,
   fib_nine_not_prime,
   fib_fifteen_not_prime, fib_nineteen_not_prime, fib_twentyone_not_prime⟩

end Omega
