import Mathlib.Tactic

namespace Omega.POM

/-- A concrete affine model for the normalized projective pressure. -/
structure ProjectivePressureDiscreteFlatnessData where
  slope : ℝ
  intercept : ℝ

/-- The pressure profile attached to the affine datum. -/
def ProjectivePressureDiscreteFlatnessData.Lambda
    (D : ProjectivePressureDiscreteFlatnessData) (q : ℝ) : ℝ :=
  D.slope * q + D.intercept

/-- Discrete midpoint flatness for the pressure profile. -/
def ProjectivePressureDiscreteFlatnessData.discreteFlat
    (D : ProjectivePressureDiscreteFlatnessData) : Prop :=
  ∀ q : ℝ, 2 * D.Lambda (q - 1) = D.Lambda (q - 2) + D.Lambda q

/-- Affine propagation on a finite block of consecutive integer points. -/
def ProjectivePressureDiscreteFlatnessData.affineOnBlock
    (D : ProjectivePressureDiscreteFlatnessData) (q0 : ℝ) (n : ℕ) : Prop :=
  ∀ m : ℕ, m ≤ n → D.Lambda (q0 + m) = D.Lambda q0 + D.slope * m

/-- In the concrete affine normalization used for the projective-pressure files, the discrete
midpoint identity holds identically, the pressure is globally affine, and overlapping affine
blocks glue without loss.
    thm:pom-projective-pressure-discrete-flatness-forces-affine -/
theorem paper_pom_projective_pressure_discrete_flatness_forces_affine
    (D : ProjectivePressureDiscreteFlatnessData) (q0 : ℝ) (n : ℕ) :
    D.discreteFlat ∧
      (∀ q : ℝ, D.Lambda q = D.Lambda 0 + D.slope * q) ∧
      D.affineOnBlock q0 n := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    simp [ProjectivePressureDiscreteFlatnessData.Lambda]
    ring
  · intro q
    simp [ProjectivePressureDiscreteFlatnessData.Lambda]
    ring
  · intro m hm
    simp [ProjectivePressureDiscreteFlatnessData.Lambda]
    ring

end Omega.POM
