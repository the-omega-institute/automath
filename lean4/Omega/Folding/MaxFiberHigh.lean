import Omega.Folding.MaxFiber

/-! ### MaxFiber high-m values (m = 8, 9, 10)

Expensive native_decide computations isolated here so that modifications to
MaxFiber.lean or downstream files do not trigger recompilation of these ~90s
computations. The .olean cache ensures this file compiles only once. -/

namespace Omega

-- m=8: X(8) = 55 elements (~5s)
-- m=9: X(9) = 89 elements (~15s)
-- m=10: X(10) = 144 elements (~60s)

private theorem cached_cMaxFiberMult_values :
    cMaxFiberMult 8 = 8 ∧ cMaxFiberMult 9 = 10 ∧ cMaxFiberMult 10 = 13 := by
  native_decide

@[simp] theorem cached_cMaxFiberMult_8 : cMaxFiberMult 8 = 8 :=
  cached_cMaxFiberMult_values.1

@[simp] theorem cached_cMaxFiberMult_9 : cMaxFiberMult 9 = 10 :=
  cached_cMaxFiberMult_values.2.1

@[simp] theorem cached_cMaxFiberMult_10 : cMaxFiberMult 10 = 13 :=
  cached_cMaxFiberMult_values.2.2

namespace X

theorem maxFiberMultiplicity_eight : maxFiberMultiplicity 8 = 8 := by rw [← cMaxFiberMult_eq]; simp
theorem maxFiberMultiplicity_nine : maxFiberMultiplicity 9 = 10 := by rw [← cMaxFiberMult_eq]; simp
theorem maxFiberMultiplicity_ten : maxFiberMultiplicity 10 = 13 := by rw [← cMaxFiberMult_eq]; simp

/-- Two-step recurrence for m = 8..10 (from base values). -/
theorem maxFiberMultiplicity_two_step_8 :
    maxFiberMultiplicity 8 = maxFiberMultiplicity 6 + maxFiberMultiplicity 4 := by
  rw [maxFiberMultiplicity_eight, maxFiberMultiplicity_six, maxFiberMultiplicity_four]
theorem maxFiberMultiplicity_two_step_9 :
    maxFiberMultiplicity 9 = maxFiberMultiplicity 7 + maxFiberMultiplicity 5 := by
  rw [maxFiberMultiplicity_nine, maxFiberMultiplicity_seven, maxFiberMultiplicity_five]
theorem maxFiberMultiplicity_two_step_10 :
    maxFiberMultiplicity 10 = maxFiberMultiplicity 8 + maxFiberMultiplicity 6 := by
  rw [maxFiberMultiplicity_ten, maxFiberMultiplicity_eight, maxFiberMultiplicity_six]

/-- Even closed form extended: D(2k) = F(k+2) for 1 ≤ k ≤ 5. -/
theorem maxFiberMultiplicity_even_ext (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 5) :
    maxFiberMultiplicity (2 * k) = Nat.fib (k + 2) := by
  interval_cases k <;> first
    | exact maxFiberMultiplicity_two
    | exact maxFiberMultiplicity_four
    | exact maxFiberMultiplicity_six
    | exact maxFiberMultiplicity_eight
    | exact maxFiberMultiplicity_ten

/-- Odd closed form extended: D(2k+1) = 2 * F(k+1) for 1 ≤ k ≤ 4. -/
theorem maxFiberMultiplicity_odd_ext (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 4) :
    maxFiberMultiplicity (2 * k + 1) = 2 * Nat.fib (k + 1) := by
  interval_cases k <;> first
    | exact maxFiberMultiplicity_three
    | exact maxFiberMultiplicity_five
    | exact maxFiberMultiplicity_seven
    | exact maxFiberMultiplicity_nine

/-- Even parity extended: k = 1..5. -/
theorem maxFiberMultiplicity_even_parity_ext (k : Nat) (hk : 1 ≤ k) (hk' : k ≤ 5) :
    Even (maxFiberMultiplicity (2 * k)) ↔ (k + 2) % 3 = 0 := by
  interval_cases k <;> simp_all only [show 2 * 1 = 2 from rfl, show 2 * 2 = 4 from rfl,
    show 2 * 3 = 6 from rfl, show 2 * 4 = 8 from rfl, show 2 * 5 = 10 from rfl,
    maxFiberMultiplicity_two, maxFiberMultiplicity_four, maxFiberMultiplicity_six,
    maxFiberMultiplicity_eight, maxFiberMultiplicity_ten] <;> decide

end X
end Omega
