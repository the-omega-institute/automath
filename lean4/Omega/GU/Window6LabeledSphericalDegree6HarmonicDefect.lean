import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.GU.Window6B3C3SphericalCubatureStrength5

namespace Omega.GU

/-- The invariant degree-`6` sum `x₁⁶ + x₂⁶ + x₃⁶`. -/
def window6A6 (x y z : ℂ) : ℂ :=
  x ^ 6 + y ^ 6 + z ^ 6

/-- The invariant degree-`6` mixed sum `∑_{i ≠ j} xᵢ⁴ xⱼ²`. -/
def window6B6 (x y z : ℂ) : ℂ :=
  x ^ 4 * y ^ 2 + x ^ 2 * y ^ 4 +
    x ^ 4 * z ^ 2 + x ^ 2 * z ^ 4 +
    y ^ 4 * z ^ 2 + y ^ 2 * z ^ 4

/-- The invariant degree-`6` triple product `x₁² x₂² x₃²`. -/
def window6C6 (x y z : ℂ) : ℂ :=
  x ^ 2 * y ^ 2 * z ^ 2

/-- The radial degree-`6` invariant `(x₁² + x₂² + x₃²)³`. -/
def window6RadialSix (x y z : ℂ) : ℂ :=
  (x ^ 2 + y ^ 2 + z ^ 2) ^ 3

/-- The universal degree-`6` harmonic defect polynomial from the paper. -/
def window6HarmonicDefectSix (x y z : ℂ) : ℂ :=
  2 * window6A6 x y z - 15 * window6B6 x y z + 180 * window6C6 x y z

/-- The explicit sixth moment of the whole degree-`5` cubature family. The three boundary-split
parameters appear only through the axis masses `(λ / 2) + (λ / 2 - tᵢ) + tᵢ = λ`. -/
noncomputable def window6DegreeSixFamilyMoment (lam t₁ t₂ t₃ x y z : ℂ) : ℂ :=
  ((lam / 2) + (lam / 2 - t₁) + t₁) * x ^ 6 +
    ((lam / 2) + (lam / 2 - t₂) + t₂) * y ^ 6 +
    ((lam / 2) + (lam / 2 - t₃) + t₃) * z ^ 6 +
    (lam / 8) *
      ((x + y) ^ 6 + (x - y) ^ 6 + (-x + y) ^ 6 + (-x - y) ^ 6 +
        (x + z) ^ 6 + (x - z) ^ 6 + (-x + z) ^ 6 + (-x - z) ^ 6 +
        (y + z) ^ 6 + (y - z) ^ 6 + (-y + z) ^ 6 + (-y - z) ^ 6)

/-- The shared sixth moment after collapsing the three positive-axis transfers. -/
noncomputable def window6DegreeSixSharedMoment (lam x y z : ℂ) : ℂ :=
  2 * lam * window6A6 x y z + (15 * lam / 2) * window6B6 x y z

set_option maxHeartbeats 400000 in
/-- Paper-facing degree-`6` spherical harmonic-defect theorem for the window-`6` labeled
cubature family: the degree-`5` cubature theorem parametrizes every admissible measure by
`(λ,t₁,t₂,t₃)`, the sixth moment is independent of `(t₁,t₂,t₃)`, and the resulting invariant
decomposes into the radial term plus the universal harmonic defect.
    thm:window6-labeled-spherical-degree6-harmonic-defect -/
theorem paper_window6_labeled_spherical_degree6_harmonic_defect :
    (∀ c : Window6SphericalLabel → ℂ, Window6DegreeFiveMomentConstraints c →
      ∃ lam t₁ t₂ t₃ : ℂ, c = window6DegreeFiveFamilyWeights lam t₁ t₂ t₃) ∧
      (∀ lam t₁ t₂ t₃ x y z : ℂ,
        window6DegreeSixFamilyMoment lam t₁ t₂ t₃ x y z =
          window6DegreeSixSharedMoment lam x y z) ∧
      (∀ lam x y z : ℂ,
        window6DegreeSixSharedMoment lam x y z =
          (15 * lam / 7) * window6RadialSix x y z -
            (lam / 14) * window6HarmonicDefectSix x y z) ∧
      (∀ x y z : ℂ,
        window6DegreeSixSharedMoment (1 / 15 : ℂ) x y z =
          (1 / 7 : ℂ) * window6RadialSix x y z -
            (1 / 210 : ℂ) * window6HarmonicDefectSix x y z) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro c hc
    exact (paper_window6_labeled_spherical_degree5_cubature_family c).1.mp hc
  · intro lam t₁ t₂ t₃ x y z
    unfold window6DegreeSixFamilyMoment window6DegreeSixSharedMoment window6A6 window6B6
    ring
  · intro lam x y z
    unfold window6DegreeSixSharedMoment window6RadialSix window6HarmonicDefectSix
      window6A6 window6B6 window6C6
    ring
  · intro x y z
    unfold window6DegreeSixSharedMoment window6RadialSix window6HarmonicDefectSix
      window6A6 window6B6 window6C6
    ring

end Omega.GU
