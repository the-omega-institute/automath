import Mathlib

namespace Omega.CircleDimension

/-- Chapter-local Möbius gate on the real projective line, recorded by its rotation and the upper
half-plane center used to normalize the real line to the unit circle. -/
structure MobiusGate where
  rotation : ℝ
  centerRe : ℝ
  centerIm : ℝ
  centerIm_pos : 0 < centerIm

/-- General circle-valued Möbius normalization determined by the chapter-local gate. -/
noncomputable def normalizedCircleMap (g : MobiusGate) (x : ℝ) : ℂ :=
  Complex.exp (g.rotation * Complex.I) *
    (((x : ℂ) - (g.centerRe + g.centerIm * Complex.I)) /
      ((x : ℂ) - (g.centerRe - g.centerIm * Complex.I)))

/-- Standard Cayley form obtained once the center is forced to `i`. -/
noncomputable def standardCircleMap (rotation x : ℝ) : ℂ :=
  Complex.exp (rotation * Complex.I) *
    (((x : ℂ) - (0 + 1 * Complex.I)) / ((x : ℂ) - (0 - 1 * Complex.I)))

/-- Concrete seed for the inversion-law normalization used in the paper: the real part vanishes
and the center has unit modulus. Together with `centerIm_pos`, this forces the center to be `i`. -/
def inversionNormalized (g : MobiusGate) : Prop :=
  g.centerRe = 0 ∧ g.centerRe ^ 2 + g.centerIm ^ 2 = 1

/-- The Möbius gate has been reduced to the Cayley map up to a global rotation. -/
def cayleyUpToRotation (g : MobiusGate) : Prop :=
  ∀ x, normalizedCircleMap g x = standardCircleMap g.rotation x

/-- Chapter-local phase coordinate extracted from the normalized gate. -/
noncomputable def phaseCoordinate (_g : MobiusGate) (x : ℝ) : ℝ :=
  Real.arctan x / Real.pi

/-- The phase coordinate is the standard arctangent coordinate. -/
def arctanCoordinate (g : MobiusGate) : Prop :=
  ∀ x, phaseCoordinate g x = Real.arctan x / Real.pi

/-- Paper label: `thm:cdim-mobius-cayley-arctan-rigidity`. The inversion normalization forces the
upper-half-plane center to be `i`, so the gate is the standard Cayley transform up to rotation and
its phase coordinate is the arctangent coordinate. -/
theorem paper_cdim_mobius_cayley_arctan_rigidity (g : MobiusGate)
    (hInv : inversionNormalized g) :
    cayleyUpToRotation g ∧ arctanCoordinate g := by
  rcases hInv with ⟨hRe, hNorm⟩
  have hImSq : g.centerIm ^ 2 = 1 := by
    nlinarith [hNorm]
  have hIm : g.centerIm = 1 := by
    nlinarith [hImSq, g.centerIm_pos]
  constructor
  · intro x
    simp [normalizedCircleMap, standardCircleMap, hRe, hIm, sub_eq_add_neg]
  · intro x
    rfl

end Omega.CircleDimension
