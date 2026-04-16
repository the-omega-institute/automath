import Mathlib.Tactic

namespace Omega.Zeta

/-- Chapter-local package for the finite-defect rationalization of the limit defect potential. The
fields record the Cayley-modulus closed form for each kernel, the exponentiation of the finite sum
into a finite product, the rational continuation of that product, the explicit zero/pole
description, and the uniqueness of the defect multiset read off from those zero/pole locations. -/
structure FiniteDefectPotentialRationalizationData where
  cayleyModulusClosedForm : Prop
  exponentialFiniteProduct : Prop
  rationalExtension : Prop
  zeroPoleDescription : Prop
  defectMultisetUniqueness : Prop
  cayleyModulusClosedForm_h : cayleyModulusClosedForm
  deriveExponentialFiniteProduct :
    cayleyModulusClosedForm → exponentialFiniteProduct
  deriveRationalExtension :
    exponentialFiniteProduct → rationalExtension
  deriveZeroPoleDescription :
    rationalExtension → zeroPoleDescription
  deriveDefectMultisetUniqueness :
    rationalExtension → zeroPoleDescription → defectMultisetUniqueness

/-- Paper-facing wrapper for the finite-defect rationalization of the limit defect potential:
expanding each kernel through the Cayley modulus closed form turns the exponentiated finite sum
into a finite product, this product extends to a rational function, and its zeros and poles occur
exactly at the shifted defect locations, so the defect multiset is uniquely recoverable.
    prop:xi-limit-defect-potential-rationalization -/
theorem paper_xi_limit_defect_potential_rationalization
    (D : FiniteDefectPotentialRationalizationData) :
    D.cayleyModulusClosedForm ∧
      D.exponentialFiniteProduct ∧
      D.rationalExtension ∧
      D.zeroPoleDescription ∧
      D.defectMultisetUniqueness := by
  have hProduct : D.exponentialFiniteProduct :=
    D.deriveExponentialFiniteProduct D.cayleyModulusClosedForm_h
  have hRational : D.rationalExtension := D.deriveRationalExtension hProduct
  have hZeroPole : D.zeroPoleDescription := D.deriveZeroPoleDescription hRational
  exact ⟨D.cayleyModulusClosedForm_h, hProduct, hRational, hZeroPole,
    D.deriveDefectMultisetUniqueness hRational hZeroPole⟩

end Omega.Zeta
