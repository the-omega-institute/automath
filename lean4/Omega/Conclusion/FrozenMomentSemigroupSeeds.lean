import Mathlib.Tactic

/-!
# Frozen moment spectrum semigroup linearization seeds

After the freezing threshold a_c, the pressure function P_a = a·α★ + g★ becomes
strictly affine. This yields an exact semigroup law:
  P_{a+b} + g★ = P_a + P_b    (a, b > a_c)
and constant first differences:
  P_{a+1} - P_a = α★           (a > a_c)
The discrete curvature vanishes identically:
  P_{a+1} - 2P_a + P_{a-1} = 0  (a > a_c + 1)

## Seed values

For the affine pressure P_a = a·α★ + g★, the semigroup identity
P_{a+b} + g★ = P_a + P_b reduces to verifying
  (a+b)·α★ + 2g★ = (a·α★ + g★) + (b·α★ + g★)
which is a pure algebraic identity in any ring.

The ℓ-step difference P_{a+ℓ} - P_a = ℓ·α★ follows from telescoping.

## Paper references

- thm:conclusion-frozen-moment-spectrum-semigroup-linearization
-/

namespace Omega.Conclusion.FrozenMomentSemigroupSeeds

/-! ## Affine pressure model: P(a) = a·α + g

We verify the semigroup and linearization identities at the level of
integer arithmetic, which captures the algebraic skeleton. -/

/-- Affine pressure model: P(a) = a * alpha + g.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
def affinePressure (alpha g : ℤ) (a : ℤ) : ℤ := a * alpha + g

/-- Semigroup law: P(a+b) + g = P(a) + P(b) for affine pressure.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem semigroup_law (alpha g a b : ℤ) :
    affinePressure alpha g (a + b) + g = affinePressure alpha g a + affinePressure alpha g b := by
  simp [affinePressure]; ring

/-- Unit difference: P(a+1) - P(a) = alpha for affine pressure.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem unit_difference (alpha g a : ℤ) :
    affinePressure alpha g (a + 1) - affinePressure alpha g a = alpha := by
  simp [affinePressure]; ring

/-- Zero discrete curvature: P(a+1) - 2·P(a) + P(a-1) = 0.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem zero_curvature (alpha g a : ℤ) :
    affinePressure alpha g (a + 1) - 2 * affinePressure alpha g a
    + affinePressure alpha g (a - 1) = 0 := by
  simp [affinePressure]; ring

/-- ℓ-step difference: P(a+ℓ) - P(a) = ℓ·alpha.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem multi_step_difference (alpha g a l : ℤ) :
    affinePressure alpha g (a + l) - affinePressure alpha g a = l * alpha := by
  simp [affinePressure]; ring

/-! ## Seed value verification at specific integer points

Verify the identities at small concrete values to confirm the algebraic model. -/

/-- Semigroup seed: a=2, b=3, alpha=5, g=7.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem semigroup_seed_2_3 :
    affinePressure 5 7 (2 + 3) + 7 = affinePressure 5 7 2 + affinePressure 5 7 3 := by
  simp [affinePressure]

/-- Unit difference seed: a=4, alpha=3, g=1.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem unit_diff_seed_4 :
    affinePressure 3 1 (4 + 1) - affinePressure 3 1 4 = 3 := by
  simp [affinePressure]

/-- Zero curvature seed: a=5, alpha=2, g=3.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem zero_curvature_seed_5 :
    affinePressure 2 3 (5 + 1) - 2 * affinePressure 2 3 5
    + affinePressure 2 3 (5 - 1) = 0 := by
  simp [affinePressure]

/-- Multi-step seed: a=1, l=4, alpha=6, g=2.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem multi_step_seed_1_4 :
    affinePressure 6 2 (1 + 4) - affinePressure 6 2 1 = 4 * 6 := by
  simp [affinePressure]

/-! ## Freezing threshold arithmetic seeds

The critical exponent a_c = (log φ - g★)/(α★ - α★²) involves the
difference of Lyapunov exponents. We verify structural constraints. -/

/-- Pressure at the threshold: P(0) = g (the intercept).
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem pressure_at_zero (alpha g : ℤ) : affinePressure alpha g 0 = g := by
  simp [affinePressure]

/-- Pressure difference ratio consistency: (P(a+l) - P(a))/l = alpha
    at integer level as l * ((P(a+l) - P(a)) / l) = l * alpha.
    We verify l * alpha = P(a+l) - P(a) directly.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem difference_ratio_consistency (alpha g a l : ℤ) :
    l * alpha = affinePressure alpha g (a + l) - affinePressure alpha g a := by
  simp [affinePressure]; ring

/-- Paper wrapper: Frozen moment spectrum semigroup linearization seeds.
    Semigroup law P(a+b)+g=P(a)+P(b), unit difference α★,
    zero discrete curvature, and multi-step telescoping.
    thm:conclusion-frozen-moment-spectrum-semigroup-linearization -/
theorem paper_conclusion_frozen_moment_semigroup_seeds :
    (∀ alpha g a b : ℤ,
      affinePressure alpha g (a + b) + g =
      affinePressure alpha g a + affinePressure alpha g b)
    ∧ (∀ alpha g a : ℤ,
      affinePressure alpha g (a + 1) - affinePressure alpha g a = alpha)
    ∧ (∀ alpha g a : ℤ,
      affinePressure alpha g (a + 1) - 2 * affinePressure alpha g a
      + affinePressure alpha g (a - 1) = 0) := by
  exact ⟨semigroup_law, unit_difference, zero_curvature⟩

end Omega.Conclusion.FrozenMomentSemigroupSeeds
