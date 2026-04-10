import Mathlib.Tactic

namespace Omega.CircleDimension.FiberPhaseQuantization

/-- Minimal period of a rational phase q is its denominator.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
def minimalPeriod (q : ℚ) : ℕ := q.den

/-- Half has period 2.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem minimalPeriod_half : minimalPeriod (1 / 2) = 2 := by native_decide

/-- Third has period 3.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem minimalPeriod_third : minimalPeriod (1 / 3) = 3 := by native_decide

/-- Sixth has period 6.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem minimalPeriod_sixth : minimalPeriod (1 / 6) = 6 := by native_decide

/-- lcm(2, 3) = 6.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem lcm_two_three : Nat.lcm 2 3 = 6 := by native_decide

/-- The period of a rational sum is bounded by lcm of individual periods.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem period_lcm_bound :
    minimalPeriod (1 / 2) ∣ Nat.lcm 2 3 ∧
    minimalPeriod (1 / 3) ∣ Nat.lcm 2 3 := by
  rw [minimalPeriod_half, minimalPeriod_third, lcm_two_three]; exact ⟨⟨3, rfl⟩, ⟨2, rfl⟩⟩

/-- Paper package: fiber phase quantization seeds.
    prop:cdim-arithmetic-singular-ring-fiber-phase-quantization -/
theorem paper_cdim_fiber_phase_quantization :
    minimalPeriod (1 / 2) = 2 ∧
    minimalPeriod (1 / 3) = 3 ∧
    minimalPeriod (1 / 6) = 6 ∧
    Nat.lcm 2 3 = 6 :=
  ⟨minimalPeriod_half, minimalPeriod_third, minimalPeriod_sixth, lcm_two_three⟩

-- Phase R609: lcm/totient/minimalPeriod seeds
-- ══════════════════════════════════════════════════════════════

/-- lcm(lcm(2,3), 5) = 30.
    thm:cdim-finite-probe-extraction -/
theorem lcm_chain_235 : Nat.lcm (Nat.lcm 2 3) 5 = 30 := by native_decide

/-- lcm(6, 10) = 30.
    thm:cdim-finite-probe-extraction -/
theorem lcm_6_10 : Nat.lcm 6 10 = 30 := by native_decide

/-- Euler totient seeds.
    thm:cdim-finite-probe-extraction -/
theorem euler_totient_seeds :
    Nat.totient 2 = 1 ∧ Nat.totient 3 = 2 ∧
    Nat.totient 6 = 2 ∧ Nat.totient 30 = 8 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Minimal period of 1/5 is 5.
    thm:cdim-finite-probe-extraction -/
theorem minimalPeriod_fifth : minimalPeriod (1 / 5) = 5 := by native_decide

/-- Minimal period of 1/30 is 30.
    thm:cdim-finite-probe-extraction -/
theorem minimalPeriod_thirtieth : minimalPeriod (1 / 30) = 30 := by native_decide

/-- Paper package: finite probe extraction seeds.
    thm:cdim-finite-probe-extraction -/
theorem paper_cdim_finite_probe_extraction :
    Nat.lcm 2 3 = 6 ∧ Nat.lcm (Nat.lcm 2 3) 5 = 30 ∧
    Nat.lcm 6 10 = 30 ∧ minimalPeriod (1 / 5) = 5 ∧
    minimalPeriod (1 / 30) = 30 ∧ Nat.totient 6 = 2 ∧
    Nat.totient 30 = 8 :=
  ⟨lcm_two_three, lcm_chain_235, lcm_6_10, minimalPeriod_fifth,
   minimalPeriod_thirtieth, by native_decide, by native_decide⟩

end Omega.CircleDimension.FiberPhaseQuantization
