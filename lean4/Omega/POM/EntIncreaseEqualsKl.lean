import Omega.POM.KLDefectIdentity

namespace Omega.POM

theorem paper_pom_ent_increase_equals_kl {X : Type*} [Fintype X] [DecidableEq X] (d : X → Nat)
    (hd : ∀ x, 0 < d x) (pi : X → Real) (mu : FiberMicrostate d → Real)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_nonneg : ∀ a, 0 ≤ mu a)
    (hpi_nonneg : ∀ x, 0 ≤ pi x) (hmu_sum : Finset.univ.sum mu = 1) :
    liftEntropy d (fiberUniformLift d pi) - liftEntropy d mu = klDiv mu (fiberUniformLift d pi) := by
  simpa using
    (paper_pom_kl_defect_identity d hd pi mu hmu_marginal hmu_nonneg hpi_nonneg hmu_sum).symm

end Omega.POM
