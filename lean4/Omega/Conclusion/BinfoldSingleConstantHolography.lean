import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-binfold-single-constant-holography`. -/
theorem paper_conclusion_binfold_single_constant_holography (Dchi Pe Dtv phi : ℝ)
    (hD : Dchi = (2 * phi - 3) / 5) (hPe : Pe = 1 / Real.sqrt 5)
    (hDtv : Dtv = 1 - 2 / Real.sqrt 5) (hphi : 2 * phi - 1 = Real.sqrt 5) :
    phi = (5 * Dchi + 3) / 2 ∧ Pe = 1 / (2 + 5 * Dchi) ∧
      Dtv = 1 - 2 / (2 + 5 * Dchi) := by
  have hden : 2 + 5 * Dchi = Real.sqrt 5 := by
    rw [hD]
    ring_nf
    linarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hD]
    ring
  · rw [hPe, hden]
  · rw [hDtv, hden]

end Omega.Conclusion
