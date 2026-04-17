import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The quartic polynomial governing the real-input-40 zero-temperature constant. -/
def realInput40ZeroTempQuartic (b : ℝ) : ℝ :=
  1 - 6 * b + 9 * b ^ 2 - b ^ 3 - b ^ 4

/-- Unified zero-temperature residue constant written in the quartic parameter `b`. -/
noncomputable def realInput40ZeroTempResidue (b : ℝ) : ℝ :=
  1 / (2 * b * (1 - b) * (6 - 18 * b + 3 * b ^ 2 + 4 * b ^ 3))

/-- The Abel finite-part kernel written directly in the quartic parameter `b`. -/
noncomputable def realInput40ZeroTempAbelKernel (b : ℝ) (m : ℕ) : ℝ :=
  if 2 ≤ m then
    Real.log ((1 - b ^ m) * (1 - 6 * b ^ m + 9 * b ^ (2 * m) - b ^ (3 * m) - b ^ (4 * m)))
  else 0

/-- The real-input-40 ground entropy, endpoint cost, pole residue, and Abel finite part all rewrite
through the same quartic parameter `b = 1 / c^2`.
    thm:conclusion-realinput40-zero-temp-quartic-constant-unification -/
theorem paper_conclusion_realinput40_zero_temp_quartic_constant_unification
    (b c Cinf logMinf : ℝ)
    (hcpos : 0 < c)
    (hbdef : b = 1 / c ^ 2)
    (hroot : realInput40ZeroTempQuartic b = 0)
    (hresidue : Cinf = realInput40ZeroTempResidue b)
    (habel :
      logMinf = Real.log Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel b m) :
    realInput40ZeroTempQuartic b = 0 ∧
      Real.log c = -((1 : ℝ) / 2) * Real.log b ∧
      Real.log (Real.goldenRatio ^ 2 / c) =
        Real.log (Real.goldenRatio ^ 2 * Real.sqrt b) ∧
      Cinf = realInput40ZeroTempResidue b ∧
      logMinf = Real.log Cinf - ∑' m : ℕ, realInput40ZeroTempAbelKernel b m := by
  have hbpos : 0 < b := by
    rw [hbdef]
    positivity
  have hsqrt : Real.sqrt b = 1 / c := by
    have hsq : (Real.sqrt b) ^ 2 = (1 / c) ^ 2 := by
      rw [Real.sq_sqrt hbpos.le, hbdef]
      field_simp [pow_two, hcpos.ne']
    have hsqrt_nonneg : 0 ≤ Real.sqrt b := Real.sqrt_nonneg b
    have hcinv_nonneg : 0 ≤ 1 / c := by positivity
    nlinarith
  refine ⟨hroot, ?_, ?_, hresidue, habel⟩
  · rw [hbdef]
    have hcne : c ≠ 0 := ne_of_gt hcpos
    have hlogb : Real.log (1 / c ^ 2) = -(2 : ℝ) * Real.log c := by
      rw [Real.log_div, Real.log_one, zero_sub, Real.log_pow]
      · ring
      · positivity
      · exact pow_ne_zero 2 hcne
    nlinarith [hlogb]
  · rw [hsqrt]
    ring_nf

end Omega.Conclusion
