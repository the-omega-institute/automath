import Mathlib.Tactic
import Omega.POM.BCDiscreteJacobianStrictification

namespace Omega.POM

noncomputable section

/-- The entropy-potential term `κ` in the concrete two-fiber Beck--Chevalley model. -/
def bcInformationEntropyPotential (a b : ℕ) : ℝ :=
  twoFiberAmgmDefect a b

/-- Scalar coboundary identity for the two concrete KL defects appearing in the strictification
package. -/
def bcInformationScalarCoboundaryIdentity (a b : ℕ) : Prop :=
  klDiv (sequentialUniformLift a b) (directUniformLift a b) = bcInformationEntropyPotential a b ∧
    klDiv middleUniformLift (strictifiedMiddleLift a b) = bcInformationEntropyPotential a b ∧
    klDiv (sequentialUniformLift a b) (directUniformLift a b) =
      klDiv middleUniformLift (strictifiedMiddleLift a b)

/-- The three discrete curvature terms all reduce to the same coboundary expression, so the
alternating Bianchi sum telescopes. -/
def bcInformationDiscreteBianchiIdentity (a b : ℕ) : Prop :=
  (klDiv (sequentialUniformLift a b) (directUniformLift a b) -
      bcInformationEntropyPotential a b) -
    (klDiv middleUniformLift (strictifiedMiddleLift a b) -
      bcInformationEntropyPotential a b) +
    (klDiv middleUniformLift (strictifiedMiddleLift a b) -
      klDiv (sequentialUniformLift a b) (directUniformLift a b)) = 0

/-- In the concrete two-fiber Beck--Chevalley model, the KL defect is exactly the entropy-potential
coboundary, and the corresponding discrete Bianchi law is the resulting telescoping identity.
    thm:pom-bc-information-stokes-coboundary -/
theorem paper_pom_bc_information_stokes_coboundary (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    bcInformationScalarCoboundaryIdentity a b ∧ bcInformationDiscreteBianchiIdentity a b := by
  have hStrict := paper_pom_bc_discrete_jacobian_strictification a b ha hb
  rcases hStrict with ⟨_, _, hMicroToMiddle, hMiddleToKappaRaw⟩
  have hMicroToKappa :
      klDiv (sequentialUniformLift a b) (directUniformLift a b) = bcInformationEntropyPotential a b :=
    by simpa [bcInformationEntropyPotential] using hMicroToMiddle.trans hMiddleToKappaRaw
  have hMiddleToKappa :
      klDiv middleUniformLift (strictifiedMiddleLift a b) = bcInformationEntropyPotential a b := by
    simpa [bcInformationEntropyPotential] using hMiddleToKappaRaw
  have hMicroEqMiddle :
      klDiv (sequentialUniformLift a b) (directUniformLift a b) =
        klDiv middleUniformLift (strictifiedMiddleLift a b) := by
    exact hMicroToMiddle
  refine ⟨⟨hMicroToKappa, hMiddleToKappa, hMicroEqMiddle⟩, ?_⟩
  unfold bcInformationDiscreteBianchiIdentity
  rw [hMicroToKappa, hMiddleToKappa]
  ring

/-- Paper-facing corollary wrapper: in the concrete two-fiber Beck--Chevalley model, the KL
defect is exactly the curvature average. `cor:pom-bc-kl-as-curvature-average` -/
theorem paper_pom_bc_kl_as_curvature_average (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    klDiv (sequentialUniformLift a b) (directUniformLift a b) = bcInformationEntropyPotential a b :=
  (paper_pom_bc_information_stokes_coboundary a b ha hb).1.1

end

end Omega.POM
