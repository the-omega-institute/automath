import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-window6-b3-rootcloud-quadratic-isotropy-forcing`. -/
theorem paper_xi_window6_b3_rootcloud_quadratic_isotropy_forcing
    (a11 a22 a33 a12 a13 a23 qs qp qm : ℝ)
    (hshort : a11 = qs ∧ a22 = qs ∧ a33 = qs)
    (hplus :
      a11 + a22 + 2 * a12 = qp ∧
        a11 + a33 + 2 * a13 = qp ∧ a22 + a33 + 2 * a23 = qp)
    (hminus :
      a11 + a22 - 2 * a12 = qm ∧
        a11 + a33 - 2 * a13 = qm ∧ a22 + a33 - 2 * a23 = qm) :
    a11 = a22 ∧
      a22 = a33 ∧
      a12 = a13 ∧
      a13 = a23 ∧
      qs = a11 ∧
      qp = 2 * a11 + 2 * a12 ∧
      qm = 2 * a11 - 2 * a12 ∧
      (qp = qm → a12 = 0 ∧ a13 = 0 ∧ a23 = 0) := by
  rcases hshort with ⟨h11, h22, h33⟩
  rcases hplus with ⟨hp12, hp13, hp23⟩
  rcases hminus with ⟨hm12, hm13, hm23⟩
  have ha11a22 : a11 = a22 := by linarith
  have ha22a33 : a22 = a33 := by linarith
  have ha12a13 : a12 = a13 := by linarith
  have ha13a23 : a13 = a23 := by linarith
  refine ⟨ha11a22, ha22a33, ha12a13, ha13a23, ?_, ?_, ?_, ?_⟩
  · linarith
  · linarith
  · linarith
  · intro hpq
    have ha12_zero : a12 = 0 := by linarith
    refine ⟨ha12_zero, ?_, ?_⟩
    · linarith
    · linarith

end Omega.Zeta
