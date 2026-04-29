import Mathlib.Tactic
import Omega.Conclusion.RealInput40LocalCramerRightTailMoreCostly
import Omega.Zeta.XiTimePart9wBasicRootUnityErrorExponentToOne

namespace Omega.Conclusion

/-- The normalized quartic jet centered at the real-input-`40` reference point. The quartic term
is encoded through the existing local Cramer jet, while the quadratic coefficient is replaced by
the audited `κ₂` closed form. -/
noncomputable def conclusion_realinput40_legendre_quadratic_field_rigidity_quartic_jet
    (δ : ℝ) : ℝ :=
  realInput40LocalCramerJet 1 0 (-24 * Omega.Zeta.xiTimePart9wBasicKappa4) δ +
    (Omega.Zeta.xiTimePart9wBasicKappa2 - (1 / 2 : ℝ)) * δ ^ 2

/-- Paper-facing package for
`thm:conclusion-realinput40-legendre-quadratic-field-rigidity`. -/
def conclusion_realinput40_legendre_quadratic_field_rigidity_statement : Prop :=
  (∀ δ : ℝ,
      conclusion_realinput40_legendre_quadratic_field_rigidity_quartic_jet δ =
        Omega.Zeta.xiTimePart9wBasicKappa2 * δ ^ 2 + Omega.Zeta.xiTimePart9wBasicKappa4 * δ ^ 4) ∧
    (∀ δ : ℝ,
      realInput40LocalCramerJet 1 0 (-24 * Omega.Zeta.xiTimePart9wBasicKappa4) δ -
          realInput40LocalCramerJet 1 0 (-24 * Omega.Zeta.xiTimePart9wBasicKappa4) (-δ) =
        0) ∧
    (∃ a₂ b₂ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa2 = (a₂ : ℝ) + (b₂ : ℝ) * Real.sqrt 5) ∧
    (∃ a₄ b₄ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa4 = (a₄ : ℝ) + (b₄ : ℝ) * Real.sqrt 5)

theorem conclusion_realinput40_legendre_quadratic_field_rigidity_kappa2_mem_qsqrt5 :
    ∃ a₂ b₂ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa2 = (a₂ : ℝ) + (b₂ : ℝ) * Real.sqrt 5 := by
  refine ⟨1791 / 200, -(3983 / 1000), ?_⟩
  unfold Omega.Zeta.xiTimePart9wBasicKappa2
  ring_nf

theorem conclusion_realinput40_legendre_quadratic_field_rigidity_kappa4_mem_qsqrt5 :
    ∃ a₄ b₄ : ℚ, Omega.Zeta.xiTimePart9wBasicKappa4 = (a₄ : ℝ) + (b₄ : ℝ) * Real.sqrt 5 := by
  refine ⟨1354428303 / 100000, -(605718497 / 100000), ?_⟩
  unfold Omega.Zeta.xiTimePart9wBasicKappa4
  ring_nf

theorem conclusion_realinput40_legendre_quadratic_field_rigidity_holds :
    conclusion_realinput40_legendre_quadratic_field_rigidity_statement := by
  refine ⟨?_, ?_, conclusion_realinput40_legendre_quadratic_field_rigidity_kappa2_mem_qsqrt5,
    conclusion_realinput40_legendre_quadratic_field_rigidity_kappa4_mem_qsqrt5⟩
  · intro δ
    unfold conclusion_realinput40_legendre_quadratic_field_rigidity_quartic_jet
    unfold realInput40LocalCramerJet
    ring
  · intro δ
    simpa using
      realInput40LocalCramerJet_difference 1 0 (-24 * Omega.Zeta.xiTimePart9wBasicKappa4) δ

def paper_conclusion_realinput40_legendre_quadratic_field_rigidity : Prop := by
  exact conclusion_realinput40_legendre_quadratic_field_rigidity_statement

end Omega.Conclusion
