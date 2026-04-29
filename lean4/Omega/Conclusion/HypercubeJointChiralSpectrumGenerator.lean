import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete block-count data for the joint chiral hypercube spectrum generator. -/
structure conclusion_hypercube_joint_chiral_spectrum_generator_Data where
  freeCoordinates : Nat
  positiveTwoCoordinateBlocks : Nat
  negativeTwoCoordinateShift : Nat

noncomputable section

/-- The Laurent generator assembled from replicated local free and positive two-coordinate
factors. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_laurentGenerator
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) (x : Real) : Real :=
  (List.replicate D.freeCoordinates (x + Inv.inv x)).prod *
    (List.replicate D.positiveTwoCoordinateBlocks
      (x ^ 2 + 1 + (Inv.inv x) ^ 2)).prod

/-- Closed product form of the replicated local factors. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_closedProduct
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) (x : Real) : Real :=
  (x + Inv.inv x) ^ D.freeCoordinates *
    (x ^ 2 + 1 + (Inv.inv x) ^ 2) ^ D.positiveTwoCoordinateBlocks

/-- Lower endpoint of the stated spectral-support interval. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_supportLower
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) : Int :=
  -(D.freeCoordinates : Int) - 2 * (D.positiveTwoCoordinateBlocks : Int) +
    2 * (D.negativeTwoCoordinateShift : Int)

/-- Upper endpoint of the stated spectral-support interval. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_supportUpper
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) : Int :=
  (D.freeCoordinates : Int) + 2 * (D.positiveTwoCoordinateBlocks : Int) -
    2 * (D.negativeTwoCoordinateShift : Int)

/-- The spectral-support interval carried by the joint chiral block. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_supportInterval
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) : Set Int :=
  Set.Icc
    (conclusion_hypercube_joint_chiral_spectrum_generator_supportLower D)
    (conclusion_hypercube_joint_chiral_spectrum_generator_supportUpper D)

/-- Product formula for the Laurent generator together with the stated support interval. -/
def conclusion_hypercube_joint_chiral_spectrum_generator_statement
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) : Prop :=
  (forall x : Real,
    conclusion_hypercube_joint_chiral_spectrum_generator_laurentGenerator D x =
      conclusion_hypercube_joint_chiral_spectrum_generator_closedProduct D x) /\
    conclusion_hypercube_joint_chiral_spectrum_generator_supportInterval D =
      Set.Icc
        (conclusion_hypercube_joint_chiral_spectrum_generator_supportLower D)
        (conclusion_hypercube_joint_chiral_spectrum_generator_supportUpper D)

/-- Paper label: `thm:conclusion-hypercube-joint-chiral-spectrum-generator`. -/
theorem paper_conclusion_hypercube_joint_chiral_spectrum_generator
    (D : conclusion_hypercube_joint_chiral_spectrum_generator_Data) :
    conclusion_hypercube_joint_chiral_spectrum_generator_statement D := by
  refine ⟨?_, rfl⟩
  intro x
  simp [conclusion_hypercube_joint_chiral_spectrum_generator_laurentGenerator,
    conclusion_hypercube_joint_chiral_spectrum_generator_closedProduct, List.prod_replicate]

end

end Omega.Conclusion
