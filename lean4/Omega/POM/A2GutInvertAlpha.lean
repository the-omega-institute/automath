import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import Omega.POM.A2GutSpectralSplitting

namespace Omega.POM

noncomputable section

/-- The quadratic constraint on `α` obtained by viewing the effective cubic as a polynomial in
`α`. -/
def pom_a2_gut_invert_alpha_quadratic (α «λ» : ℝ) : Prop :=
  2 * α ^ 2 - («λ» ^ 2 + 2 * «λ») * α + «λ» ^ 2 * («λ» - 1) = 0

/-- The lower algebraic branch used for the explicit inverse. -/
def pom_a2_gut_invert_alpha_branch («λ» : ℝ) : ℝ :=
  «λ» / 4 * ((«λ» + 2) - Real.sqrt ((«λ» - 2) ^ 2 + 8))

/-- Paper label: `cor:pom-a2-gut-invert-alpha`.

The effective cubic relation from the spectral-splitting proposition is equivalently a quadratic
constraint in `α`, and the stated lower branch is normalized at the rank-one endpoint. -/
def pom_a2_gut_invert_alpha_statement : Prop :=
  (∀ α «λ» : ℝ,
    Matrix.det (pom_a2_gut_spectral_splitting_char_matrix α «λ») = 0 ↔
      pom_a2_gut_invert_alpha_quadratic α «λ») ∧
    pom_a2_gut_invert_alpha_branch 0 = 0

theorem paper_pom_a2_gut_invert_alpha : pom_a2_gut_invert_alpha_statement := by
  refine ⟨?_, ?_⟩
  · intro α lam
    rw [pom_a2_gut_spectral_splitting_det]
    unfold pom_a2_gut_invert_alpha_quadratic
    constructor <;> intro h <;> nlinarith
  · simp [pom_a2_gut_invert_alpha_branch]

end

end Omega.POM
