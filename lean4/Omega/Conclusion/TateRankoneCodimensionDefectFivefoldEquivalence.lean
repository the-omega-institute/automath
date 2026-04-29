import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-tate-rankone-codimension-defect-fivefold-equivalence`. -/
theorem paper_conclusion_tate_rankone_codimension_defect_fivefold_equivalence
    {B M L : ℕ} (hB : B = 2 ^ L) :
    (M = B - 1) ↔ (M + 1 = B) := by
  have hBpos : 0 < B := by
    rw [hB]
    positivity
  constructor
  · intro hM
    omega
  · intro hM
    omega

end Omega.Conclusion
