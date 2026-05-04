import Mathlib.Tactic

namespace Omega.Conclusion

structure conclusion_leyang_xh_ed_prym_elliptic_isogeny_data where
  genusXH : ℕ
  genusED : ℕ
  prymDimension : ℕ
  jacobianSplittingComparison : Bool
  polarizationType : ℕ
  polarizationDegree : ℕ

namespace conclusion_leyang_xh_ed_prym_elliptic_isogeny_data

def conclusion_leyang_xh_ed_prym_elliptic_isogeny_cover_package
    (D : conclusion_leyang_xh_ed_prym_elliptic_isogeny_data) : Prop :=
  D.genusXH = 2 ∧
    D.genusED = 1 ∧
    D.prymDimension = D.genusXH - D.genusED ∧
    D.jacobianSplittingComparison = true ∧
    D.polarizationType = 2 ∧
    D.polarizationDegree = D.polarizationType ^ 2

def conclusion_leyang_xh_ed_prym_elliptic_isogeny_statement
    (D : conclusion_leyang_xh_ed_prym_elliptic_isogeny_data) : Prop :=
  D.prymDimension = 1 ∧
    D.jacobianSplittingComparison = true ∧
    D.polarizationType = 2 ∧
    D.polarizationDegree = 4

end conclusion_leyang_xh_ed_prym_elliptic_isogeny_data

/-- Paper label: `thm:conclusion-leyang-xh-ed-prym-elliptic-isogeny`. -/
theorem paper_conclusion_leyang_xh_ed_prym_elliptic_isogeny
    (D : conclusion_leyang_xh_ed_prym_elliptic_isogeny_data)
    (hD : D.conclusion_leyang_xh_ed_prym_elliptic_isogeny_cover_package) :
    D.conclusion_leyang_xh_ed_prym_elliptic_isogeny_statement := by
  rcases hD with ⟨hXH, hED, hdim, hsplit, htype, hdeg⟩
  refine ⟨?_, hsplit, htype, ?_⟩
  · rw [hdim, hXH, hED]
  · rw [hdeg, htype]
    norm_num

end Omega.Conclusion
