import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- A `2 x 2` weighted kernel used as a concrete four-entry seed for the real-input-40 reparameterization. -/
abbrev RealInput40Matrix := Fin 2 → Fin 2 → ℝ

/-- The fourth coordinate is the edge phase difference `χ = φ_e - φ_2`. -/
def realInput40Chi (phiE phi2 : ℝ) : ℝ :=
  phiE - phi2

/-- The original four-parameter exponent with coordinates `(φ_e, φ_-, φ_2, χ)`. -/
def realInput40Exponent (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) (i j : Fin 2) : ℝ :=
  thetaE i j * phiE + thetaChi i j * realInput40Chi phiE phi2 +
    thetaMinus i j * phiMinus + theta2 i j * phi2

/-- The linearly reparameterized exponent after eliminating `χ`. -/
def realInput40ReparamExponent (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) (i j : Fin 2) : ℝ :=
  (thetaE i j + thetaChi i j) * phiE + thetaMinus i j * phiMinus +
    (theta2 i j - thetaChi i j) * phi2

/-- Entrywise kernel with the original `χ`-coordinate. -/
def realInput40WeightedMatrix (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : RealInput40Matrix :=
  fun i j => Real.exp (realInput40Exponent thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 i j)

/-- Entrywise kernel after the `χ` reparameterization. -/
def realInput40WeightedMatrixReparam (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : RealInput40Matrix :=
  fun i j =>
    Real.exp (realInput40ReparamExponent thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 i j)

/-- A concrete spectral-radius wrapper: the total edge weight. -/
def realInput40SpectralRadius (M : RealInput40Matrix) : ℝ :=
  ∑ i, ∑ j, M i j

/-- Zeta wrapper around the concrete spectral radius. -/
def realInput40Zeta (M : RealInput40Matrix) : ℝ :=
  1 + realInput40SpectralRadius M

/-- Log wrapper around the concrete zeta quantity. -/
def realInput40LogM (M : RealInput40Matrix) : ℝ :=
  Real.log (realInput40Zeta M)

/-- Entrywise equality of the original and reparameterized weighted kernels. -/
def realInput40MatrixReparametrized (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : Prop :=
  realInput40WeightedMatrix thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 =
    realInput40WeightedMatrixReparam thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2

/-- Equality of the spectral-radius wrappers after reparameterization. -/
def realInput40SpectralRadiusReparametrized (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : Prop :=
  realInput40SpectralRadius
      (realInput40WeightedMatrix thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2) =
    realInput40SpectralRadius
      (realInput40WeightedMatrixReparam thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2)

/-- Equality of the zeta wrappers after reparameterization. -/
def realInput40ZetaReparametrized (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : Prop :=
  realInput40Zeta (realInput40WeightedMatrix thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2) =
    realInput40Zeta
      (realInput40WeightedMatrixReparam thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2)

/-- Equality of the log wrappers after reparameterization. -/
def realInput40LogMReparametrized (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) : Prop :=
  realInput40LogM (realInput40WeightedMatrix thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2) =
    realInput40LogM
      (realInput40WeightedMatrixReparam thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2)

lemma realInput40Exponent_rewrite (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix)
    (phiE phiMinus phi2 : ℝ) (i j : Fin 2) :
    realInput40Exponent thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 i j =
      realInput40ReparamExponent thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 i j := by
  simp [realInput40Exponent, realInput40ReparamExponent, realInput40Chi]
  ring

/-- Paper label: `prop:chi-reparam-4d`.
Substituting `χ = φ_e - φ_2` rewrites each edge exponent as
`(θ_e + θ_χ) φ_e + θ_- φ_- + (θ_2 - θ_χ) φ_2`, so the weighted matrix and the derived
spectral-radius, zeta, and log wrappers all agree. -/
theorem paper_real_input_40_chi_reparam_4d
    (thetaE thetaChi thetaMinus theta2 : RealInput40Matrix) (phiE phiMinus phi2 : ℝ) :
    realInput40MatrixReparametrized thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 ∧
      realInput40SpectralRadiusReparametrized thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 ∧
      realInput40ZetaReparametrized thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 ∧
      realInput40LogMReparametrized thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 := by
  have hMatrix :
      realInput40MatrixReparametrized thetaE thetaChi thetaMinus theta2 phiE phiMinus phi2 := by
    funext i j
    rw [realInput40WeightedMatrix, realInput40WeightedMatrixReparam]
    rw [realInput40Exponent_rewrite]
  refine ⟨hMatrix, ?_, ?_, ?_⟩
  · exact congrArg realInput40SpectralRadius hMatrix
  · exact congrArg realInput40Zeta hMatrix
  · exact congrArg realInput40LogM hMatrix

end

end Omega.SyncKernelWeighted
