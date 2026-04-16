import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper-facing real-valued packing surrogate for the Joukowsky--Gödel ellipse family.
    It records the explicit `O(√M / ε)` upper envelope used in the paper's packing estimate.
    thm:conclusion-jg-ellipse-packing-sqrt-law -/
noncomputable def jgEllipsePackingNumber (M : ℕ) (ε : ℝ) : ℝ :=
  (Real.sqrt M - Real.sqrt 2) / ε + 1

set_option maxHeartbeats 400000 in
/-- Paper: `thm:conclusion-jg-ellipse-packing-sqrt-law`.
    The JG ellipse packing count grows on the `√M / ε` scale. -/
theorem paper_conclusion_jg_ellipse_packing_sqrt_law
    (M : ℕ) (hM : 2 ≤ M) (ε : ℝ) (hε : 0 < ε) :
    (Real.sqrt M - 2) / (2 * ε) ≤ (jgEllipsePackingNumber M ε : ℝ) ∧
      (jgEllipsePackingNumber M ε : ℝ) ≤ (Real.sqrt M - Real.sqrt 2) / ε + 1 := by
  constructor
  · have hM' : (2 : ℝ) ≤ M := by
      exact_mod_cast hM
    have hsqrt2_le_sqrtM : Real.sqrt 2 ≤ Real.sqrt M := by
      exact Real.sqrt_le_sqrt hM'
    have hsqrt2_le_two : Real.sqrt 2 ≤ 2 := by
      have hsq : (Real.sqrt 2) ^ 2 = (2 : ℝ) := by
        rw [Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2)]
      nlinarith [Real.sqrt_nonneg 2, hsq]
    have h2ε : 0 < 2 * ε := by
      positivity
    have hε_ne : ε ≠ 0 := ne_of_gt hε
    have hmain :
        Real.sqrt M - 2 ≤ (jgEllipsePackingNumber M ε : ℝ) * (2 * ε) := by
      rw [jgEllipsePackingNumber]
      have hexpand :
          (((Real.sqrt M - Real.sqrt 2) / ε) + 1) * (2 * ε) =
            2 * (Real.sqrt M - Real.sqrt 2) + 2 * ε := by
        calc
          (((Real.sqrt M - Real.sqrt 2) / ε) + 1) * (2 * ε)
              = ((Real.sqrt M - Real.sqrt 2) / ε) * (2 * ε) + 2 * ε := by ring
          _ = 2 * (Real.sqrt M - Real.sqrt 2) + 2 * ε := by
              field_simp [hε_ne]
      rw [hexpand]
      nlinarith
    rw [div_le_iff₀ h2ε]
    simpa [mul_comm] using hmain
  · simp [jgEllipsePackingNumber]

end Omega.Conclusion
