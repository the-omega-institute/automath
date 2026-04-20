import Omega.POM.ValPolynomialSemantics

namespace Omega.POM

/-- Extensional equality of value-layer words is decidable because their semantics is a finite
tuple of multivariate polynomials with decidable equality on each coordinate.
    thm:pom-val-extensional-equivalence-decidable -/
noncomputable def paper_pom_val_extensional_equivalence_decidable {n k1 k2 : Nat} (w1 : ValWord n k1)
    (w2 : ValWord n k2) : Decidable (wordPolynomialMap w1 = wordPolynomialMap w2) := by
  infer_instance

end Omega.POM
