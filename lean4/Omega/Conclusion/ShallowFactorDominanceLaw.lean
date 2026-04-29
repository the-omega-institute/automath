import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-shallow-factor-dominance-law`. -/
theorem paper_conclusion_shallow_factor_dominance_law {hPhi hPsi hChi c Ndet : ℝ}
    (hPhi_pos : 0 < hPhi) (hPsi_pos : 0 < hPsi) (hChi_eq : hChi = min hPhi hPsi)
    (hthreshold : c * hChi⁻¹ ≤ Ndet) :
    hChi = min hPhi hPsi ∧ c * max hPhi⁻¹ hPsi⁻¹ ≤ Ndet := by
  constructor
  · exact hChi_eq
  · have hinv_min : (min hPhi hPsi)⁻¹ = max hPhi⁻¹ hPsi⁻¹ := by
      by_cases hle : hPhi ≤ hPsi
      · have hinv_le : hPsi⁻¹ ≤ hPhi⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hPhi_pos hle
        simp [min_eq_left hle, max_eq_left hinv_le]
      · have hle' : hPsi ≤ hPhi := le_of_not_ge hle
        have hinv_le : hPhi⁻¹ ≤ hPsi⁻¹ := by
          simpa [one_div] using one_div_le_one_div_of_le hPsi_pos hle'
        simp [min_eq_right hle', max_eq_right hinv_le]
    simpa [hChi_eq, hinv_min] using hthreshold

end Omega.Conclusion
