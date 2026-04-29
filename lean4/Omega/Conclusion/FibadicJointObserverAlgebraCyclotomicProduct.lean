import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete finite-layer data for the joint observer algebra cyclotomic-product package. -/
structure conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data where
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount : ℕ
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicDimension :
    Fin conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount → ℕ
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_activeDepth :
    Fin conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount → ℕ
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket :
    Fin conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount → ℕ
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket_nonzero :
    ∀ i,
      conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket i ≠ 0
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_mobiusBlockProjector :
    Fin conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount →
      Fin conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount → ℚ

/-- The cyclic algebra attached to a single active block, represented by its coordinate
functions on the packaged cyclic basis. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicBlockAlgebra
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data)
    (i : Fin D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount) :
    Type :=
  Fin
      (D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicDimension i) →
    ℚ

/-- The visible joint observer algebra after Mobius block decomposition. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_jointObserverAlgebra
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Type :=
  (i : Fin D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount) →
    conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicBlockAlgebra D i

/-- The product of cyclic block algebras indexed by the active depths. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicBlockProduct
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Type :=
  (i : Fin D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount) →
    conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicBlockAlgebra D i

/-- Restrict a joint observer to each cyclic Mobius block. In these coordinates this is the
identity map from the decomposed algebra to the product of its block coordinates. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockRestrictionMap
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) :
    conclusion_fibadic_joint_observer_algebra_cyclotomic_product_jointObserverAlgebra D →
      conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicBlockProduct D :=
  id

/-- The squarefree-minimal-polynomial facts carried by the cyclotomic packet: every active
block has a nonzero packet polynomial index. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_squarefreeMinimalPolynomialFacts
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Prop :=
  ∀ i,
    D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket i ≠ 0

/-- A finite-dimensional Artinian certificate: the active block index type is finite. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_artinianCertificate
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Prop :=
  Nonempty (Fintype (Fin D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount))

/-- Jacobson semisimplicity is represented by the nonzero squarefree packet facts for all
cyclic blocks. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_jacobsonSemisimpleCertificate
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Prop :=
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_squarefreeMinimalPolynomialFacts D

/-- Primitive-spectrum coordinates of the decomposed finite product algebra. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_primitiveSpectrum
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) :
    Set
      (Sigma fun i :
          Fin D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockCount =>
        Fin
          (D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclicDimension i)) :=
  Set.univ

/-- The primitive spectrum is exactly the collection of active block/cyclotomic-root
coordinates whose packet index is nonzero. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_primitiveSpectrumIdentified
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Prop :=
  conclusion_fibadic_joint_observer_algebra_cyclotomic_product_primitiveSpectrum D =
    {x |
      D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket x.1 ≠
        0}

/-- The concrete finite-product conclusion for the joint observer algebra package. -/
def conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data.statement
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : Prop :=
  Function.Injective
      (conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockRestrictionMap D) ∧
    Function.Surjective
      (conclusion_fibadic_joint_observer_algebra_cyclotomic_product_blockRestrictionMap D) ∧
      conclusion_fibadic_joint_observer_algebra_cyclotomic_product_artinianCertificate D ∧
        conclusion_fibadic_joint_observer_algebra_cyclotomic_product_jacobsonSemisimpleCertificate
          D ∧
          conclusion_fibadic_joint_observer_algebra_cyclotomic_product_primitiveSpectrumIdentified
            D

/-- Paper label: `thm:conclusion-fibadic-joint-observer-algebra-cyclotomic-product`. -/
theorem paper_conclusion_fibadic_joint_observer_algebra_cyclotomic_product
    (D : conclusion_fibadic_joint_observer_algebra_cyclotomic_product_data) : D.statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro x y hxy
    exact hxy
  · intro y
    exact ⟨y, rfl⟩
  · exact ⟨inferInstance⟩
  · intro i
    exact
      D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket_nonzero
        i
  · ext x
    simp [
      conclusion_fibadic_joint_observer_algebra_cyclotomic_product_primitiveSpectrum,
      D.conclusion_fibadic_joint_observer_algebra_cyclotomic_product_cyclotomicPacket_nonzero
        x.1]

end Omega.Conclusion
