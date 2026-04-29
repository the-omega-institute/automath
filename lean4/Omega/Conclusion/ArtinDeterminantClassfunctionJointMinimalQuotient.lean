import Omega.Conclusion.PrimitiveMinimalCarrierQuotient

namespace Omega.Conclusion

open scoped BigOperators

/-- The joint active set of determinant and class-function channels. -/
def conclusion_artin_determinant_classfunction_joint_minimal_quotient_active
    {X : Type*} [DecidableEq X] (detActive classActive : Finset X) : Finset X :=
  detActive ∪ classActive

/-- The joint visible kernel is the intersection of all active determinant and class-function
channel kernels. -/
def conclusion_artin_determinant_classfunction_joint_minimal_quotient_kernel
    {G X : Type*} [CommGroup G] [DecidableEq X] (detActive classActive : Finset X)
    (χ : X → G → Complex) (hχ1 : ∀ x, χ x 1 = 1)
    (hχmul : ∀ x g h, χ x (g * h) = χ x g * χ x h) :
    Subgroup G :=
  primitiveMinimalCarrierKernel
    (conclusion_artin_determinant_classfunction_joint_minimal_quotient_active
      detActive classActive) χ hχ1 hχmul

/-- Concrete statement of the joint determinant/class-function minimal quotient criterion. -/
def conclusion_artin_determinant_classfunction_joint_minimal_quotient_statement : Prop :=
  ∀ {G X : Type*} [Fintype G] [CommGroup G]
    [DecidableEq X]
    (detActive classActive : Finset X) (χ : X → G → Complex)
    (coeff : X → Complex) (profile : G → Complex)
    (hχ1 : ∀ x, χ x 1 = 1)
    (hχmul : ∀ x g h, χ x (g * h) = χ x g * χ x h)
    (_hprofile :
      ∀ g,
        profile g =
          Finset.sum
            (conclusion_artin_determinant_classfunction_joint_minimal_quotient_active
              detActive classActive)
            (fun x => χ x g * coeff x))
    (_hcoeff_unique :
      ∀ k,
        (∀ c,
            Finset.sum
              (conclusion_artin_determinant_classfunction_joint_minimal_quotient_active
                detActive classActive)
              (fun x => χ x c * ((χ x k - 1) * coeff x)) = 0) →
          k ∈
            conclusion_artin_determinant_classfunction_joint_minimal_quotient_kernel
              detActive classActive χ hχ1 hχmul),
    let H :=
      conclusion_artin_determinant_classfunction_joint_minimal_quotient_kernel
        detActive classActive χ hχ1 hχmul
    PrimitiveCarrierInvariant H profile ∧
      PrimitiveCarrierFactorsThroughQuotient H profile ∧
      (∀ K : Subgroup G, PrimitiveCarrierInvariant K profile ↔ K ≤ H) ∧
      PrimitiveCarrierSupportOnQuotient H detActive χ ∧
      PrimitiveCarrierSupportOnQuotient H classActive χ

/-- Paper label: `thm:conclusion-artin-determinant-classfunction-joint-minimal-quotient`. -/
theorem paper_conclusion_artin_determinant_classfunction_joint_minimal_quotient :
    conclusion_artin_determinant_classfunction_joint_minimal_quotient_statement := by
  intro G X _ _ _ detActive classActive χ coeff profile hχ1 hχmul hprofile hcoeff_unique
  let active :=
    conclusion_artin_determinant_classfunction_joint_minimal_quotient_active
      detActive classActive
  let H :=
    conclusion_artin_determinant_classfunction_joint_minimal_quotient_kernel
      detActive classActive χ hχ1 hχmul
  rcases paper_conclusion_primitive_minimal_carrier_quotient active χ coeff profile hχ1
      hχmul hprofile hcoeff_unique with ⟨hInv, hFactors, hMax, hSupport⟩
  refine ⟨hInv, hFactors, ?_, ?_, ?_⟩
  · intro K
    constructor
    · intro hK
      exact hMax K hK
    · intro hK c h hh
      exact hInv c h (hK hh)
  · intro x hx h hh
    exact hSupport x (Finset.mem_union_left classActive hx) h hh
  · intro x hx h hh
    exact hSupport x (Finset.mem_union_right detActive hx) h hh

end Omega.Conclusion
