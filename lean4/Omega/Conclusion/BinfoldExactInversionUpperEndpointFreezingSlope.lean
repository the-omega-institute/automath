import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Log
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- Exact inversion at budget `B` means that every visible fiber is bounded by `2^B`. -/
def binfoldExactInversionAdmits (d : α → ℕ) (B : ℕ) : Prop :=
  ∀ x, d x ≤ 2 ^ B

/-- The largest visible fiber multiplicity. -/
def binfoldMaxFiber (d : α → ℕ) : ℕ :=
  Finset.univ.sup d

/-- The upper-endpoint bit budget extracted from a geometric max-fiber law `M_m = b^m`. -/
noncomputable def binfoldUpperEndpointBudget (b m : ℕ) : ℕ :=
  Nat.ceil ((m : ℝ) * Real.logb 2 (b : ℝ))

/-- The freezing slope attached to the same extremal exponent. -/
noncomputable def binfoldFreezingSlope (b : ℕ) : ℝ :=
  Real.logb 2 (b : ℝ)

/-- The affine freezing-pressure ray with slope `log₂ b`. -/
noncomputable def binfoldFreezingPressureRay (b : ℕ) (gStar beta : ℝ) : ℝ :=
  gStar + beta * binfoldFreezingSlope b

omit [DecidableEq α] in
theorem le_binfoldMaxFiber (d : α → ℕ) (x : α) :
    d x ≤ binfoldMaxFiber d := by
  unfold binfoldMaxFiber
  exact Finset.le_sup (Finset.mem_univ x)

theorem binfoldExactInversionAdmits_iff (d : α → ℕ) (B : ℕ) :
    binfoldExactInversionAdmits d B ↔ binfoldMaxFiber d ≤ 2 ^ B := by
  constructor
  · intro h
    unfold binfoldMaxFiber
    exact Finset.sup_le fun x _ => h x
  · intro h x
    exact (le_binfoldMaxFiber d x).trans h

theorem binfoldExactInversionAdmits_clog (d : α → ℕ) :
    binfoldExactInversionAdmits d (Nat.clog 2 (binfoldMaxFiber d)) := by
  rw [binfoldExactInversionAdmits_iff]
  exact Nat.le_pow_clog (by norm_num) _

theorem clog_binfoldMaxFiber_minimal (d : α → ℕ) {B : ℕ}
    (hB : binfoldExactInversionAdmits d B) :
    Nat.clog 2 (binfoldMaxFiber d) ≤ B := by
  rw [binfoldExactInversionAdmits_iff] at hB
  exact Nat.clog_le_of_le_pow hB

theorem binfoldUpperEndpointBudget_formula (b m : ℕ) :
    binfoldUpperEndpointBudget b m = Nat.ceil (Real.logb 2 ((b : ℝ) ^ m)) := by
  rw [binfoldUpperEndpointBudget, Real.logb_pow]

theorem binfoldUpperEndpointBudget_limit (b : ℕ) (hb : 1 ≤ b) :
    Tendsto (fun m : ℕ => (binfoldUpperEndpointBudget b m : ℝ) / m)
      atTop (nhds (binfoldFreezingSlope b)) := by
  have hlog_nonneg : 0 ≤ binfoldFreezingSlope b := by
    unfold binfoldFreezingSlope
    exact Real.logb_nonneg (by norm_num) (by exact_mod_cast hb)
  simpa [binfoldUpperEndpointBudget, binfoldFreezingSlope, mul_comm, mul_left_comm, mul_assoc] using
    (tendsto_nat_ceil_mul_div_atTop (R := ℝ) (a := Real.logb 2 (b : ℝ)) hlog_nonneg).comp
      tendsto_natCast_atTop_atTop

theorem binfoldFreezingPressureRay_slope (b : ℕ) (gStar beta : ℝ) :
    binfoldFreezingPressureRay b gStar beta - binfoldFreezingPressureRay b gStar 0 =
      beta * binfoldFreezingSlope b := by
  unfold binfoldFreezingPressureRay
  ring

/-- The exact-inversion upper endpoint is determined by the largest fiber `M`, its minimal binary
budget is `⌈log₂ M⌉`, and along a geometric family `M_m = b^m` the normalized budget converges to
the same slope as the affine freezing-pressure ray.
    thm:conclusion-binfold-exact-inversion-upper-endpoint-freezing-slope -/
theorem paper_conclusion_binfold_exact_inversion_upper_endpoint_freezing_slope
    (d : α → ℕ) (b : ℕ) (hb : 1 ≤ b) :
    let M := binfoldMaxFiber d
    (∀ B : ℕ, binfoldExactInversionAdmits d B ↔ M ≤ 2 ^ B) ∧
      binfoldExactInversionAdmits d (Nat.clog 2 M) ∧
      (∀ B : ℕ, binfoldExactInversionAdmits d B → Nat.clog 2 M ≤ B) ∧
      (∀ m : ℕ, binfoldUpperEndpointBudget b m = Nat.ceil (Real.logb 2 ((b : ℝ) ^ m))) ∧
      Tendsto (fun m : ℕ => (binfoldUpperEndpointBudget b m : ℝ) / m)
        atTop (nhds (binfoldFreezingSlope b)) ∧
      (∀ gStar beta : ℝ,
        binfoldFreezingPressureRay b gStar beta - binfoldFreezingPressureRay b gStar 0 =
          beta * binfoldFreezingSlope b) := by
  dsimp
  refine ⟨?_, binfoldExactInversionAdmits_clog d, ?_, binfoldUpperEndpointBudget_formula b,
    binfoldUpperEndpointBudget_limit b hb, ?_⟩
  · intro B
    exact binfoldExactInversionAdmits_iff d B
  · intro B hB
    exact clog_binfoldMaxFiber_minimal d hB
  · intro gStar beta
    exact binfoldFreezingPressureRay_slope b gStar beta

end Omega.Conclusion
