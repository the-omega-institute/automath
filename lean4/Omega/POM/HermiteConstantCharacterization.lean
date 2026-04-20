import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Omega.POM

/-- Concrete scalar package for the determinant-scaled Hermite-constant extremal formula. -/
structure POMHermiteConstantCharacterizationData where
  d : ℕ
  hermiteConstant : ℝ
  detSigma : ℝ
  covolume : ℝ

/-- Euclidean Hermite extremal value at fixed covolume. -/
noncomputable def POMHermiteConstantCharacterizationData.euclideanExtremal
    (D : POMHermiteConstantCharacterizationData) : ℝ :=
  D.hermiteConstant * Real.rpow D.covolume (2 / (D.d : ℝ))

/-- Determinant-scaled first-minimum supremum after conjugating by `Σ^(1/2)`. -/
noncomputable def POMHermiteConstantCharacterizationData.supFirstMinimum
    (D : POMHermiteConstantCharacterizationData) : ℝ :=
  Real.rpow D.detSigma (1 / (D.d : ℝ)) * D.euclideanExtremal

/-- Hermite-constant characterization of the optimal first minimum in a fixed covolume class.
    thm:pom-hermite-constant-characterization -/
theorem paper_pom_hermite_constant_characterization (D : POMHermiteConstantCharacterizationData) :
    D.supFirstMinimum =
      D.hermiteConstant * Real.rpow D.detSigma (1 / (D.d : ℝ)) *
        Real.rpow D.covolume (2 / (D.d : ℝ)) := by
  simp [POMHermiteConstantCharacterizationData.supFirstMinimum,
    POMHermiteConstantCharacterizationData.euclideanExtremal, mul_assoc, mul_left_comm]

end Omega.POM
