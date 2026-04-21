import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Conclusion

/-- The dominant pole used in the real-input-40 Artin-shadow factorization. -/
noncomputable def derivedArtinShadowPole : ℝ :=
  (Real.goldenRatio⁻¹) ^ 2

/-- Denominator of the trivial Artin-shadow factor. -/
def derivedArtinShadowTrivialDen (z : ℝ) : ℝ :=
  (1 - z) ^ 2 * (1 + z) ^ 3

/-- Denominator of the even Artin-shadow factor. -/
def derivedArtinShadowEvenDen (z : ℝ) : ℝ :=
  1 - 3 * z + z ^ 2

/-- Denominator of the sign/character Artin-shadow factor. -/
def derivedArtinShadowChiDen (z : ℝ) : ℝ :=
  1 + z - z ^ 2

/-- The finite-part polynomial contributed by the trivial channel. -/
def derivedArtinShadowFinitePartPolynomial (z : ℝ) : ℝ :=
  -z + 3 * z ^ 2

/-- Paper label wrapper for the constant-layer compression at the dominant real-input-40 pole.
    thm:derived-artin-shadow-constant-layer-compression -/
def paper_derived_artin_shadow_constant_layer_compression : Prop := by
  exact
    derivedArtinShadowEvenDen derivedArtinShadowPole = 0 ∧
      derivedArtinShadowTrivialDen derivedArtinShadowPole ≠ 0 ∧
      derivedArtinShadowChiDen derivedArtinShadowPole ≠ 0 ∧
      derivedArtinShadowFinitePartPolynomial derivedArtinShadowPole =
        9 - 4 * Real.sqrt 5

end Omega.Conclusion
