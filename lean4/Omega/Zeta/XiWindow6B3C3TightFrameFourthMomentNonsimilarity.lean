import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic
import Omega.Zeta.XiWindow6C3QuadraticEnergyEquipartition

namespace Omega.Zeta

/-- The six short `B₃` roots `± eᵢ`. -/
def xiWindow6B3ShortRoots : List XiWindow6Root :=
  [((1 : ℤ), 0, 0), ((-1 : ℤ), 0, 0), (0, (1 : ℤ), 0), (0, (-1 : ℤ), 0), (0, 0, (1 : ℤ)),
    (0, 0, (-1 : ℤ))]

/-- The full `B₃` root list: short roots `± eᵢ` plus long roots `± eᵢ ± eⱼ`. -/
def xiWindow6B3Roots : List XiWindow6Root :=
  xiWindow6B3ShortRoots ++ xiWindow6ShortRoots

/-- The full `C₃` root list: long roots `± 2 eᵢ` plus short roots `± eᵢ ± eⱼ`. -/
def xiWindow6C3Roots : List XiWindow6Root :=
  xiWindow6LongRoots ++ xiWindow6ShortRoots

/-- The quadratic directional moment of the concrete `B₃` dictionary. -/
def xiWindow6B3QuadraticMoment (x y z : ℤ) : ℤ :=
  (xiWindow6B3Roots.map fun v => (xiRootProbe x y z v) ^ 2).sum

/-- The quadratic directional moment of the concrete `C₃` dictionary. -/
def xiWindow6C3QuadraticMoment (x y z : ℤ) : ℤ :=
  (xiWindow6C3Roots.map fun v => (xiRootProbe x y z v) ^ 2).sum

/-- The fourth directional moment of the concrete `B₃` dictionary. -/
def xiWindow6B3FourthMoment (x y z : ℤ) : ℤ :=
  (xiWindow6B3Roots.map fun v => (xiRootProbe x y z v) ^ 4).sum

/-- The fourth directional moment of the concrete `C₃` dictionary. -/
def xiWindow6C3FourthMoment (x y z : ℤ) : ℤ :=
  (xiWindow6C3Roots.map fun v => (xiRootProbe x y z v) ^ 4).sum

/-- Explicit quadratic/frame and fourth-moment formulas for the window-`6` `B₃/C₃` dictionaries,
plus the resulting obstruction to a single global Euclidean rescaling between them. -/
def XiWindow6B3C3TightFrameFourthMomentNonsimilarityStatement : Prop :=
  (∀ x y z : ℤ, xiWindow6B3QuadraticMoment x y z = 10 * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    (∀ x y z : ℤ, xiWindow6C3QuadraticMoment x y z = 16 * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    (∀ x y z : ℤ,
      xiWindow6B3FourthMoment x y z =
        10 * (x ^ 4 + y ^ 4 + z ^ 4) + 24 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)) ∧
    (∀ x y z : ℤ,
      xiWindow6C3FourthMoment x y z =
        40 * (x ^ 4 + y ^ 4 + z ^ 4) + 24 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2)) ∧
    ¬ ∃ s : ℝ, 0 < s ∧
      ∀ x y z : ℤ, (xiWindow6C3FourthMoment x y z : ℝ) = s ^ 4 * (xiWindow6B3FourthMoment x y z : ℝ)

private theorem xiWindow6B3QuadraticMoment_closed (x y z : ℤ) :
    xiWindow6B3QuadraticMoment x y z = 10 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [xiWindow6B3QuadraticMoment, xiWindow6B3Roots, xiWindow6B3ShortRoots, xiWindow6ShortRoots,
    xiRootProbe, xiRootX, xiRootY, xiRootZ]
  ring_nf

private theorem xiWindow6C3QuadraticMoment_closed (x y z : ℤ) :
    xiWindow6C3QuadraticMoment x y z = 16 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [xiWindow6C3QuadraticMoment, xiWindow6C3Roots, xiWindow6LongRoots, xiWindow6ShortRoots,
    xiRootProbe, xiRootX, xiRootY, xiRootZ]
  ring_nf

private theorem xiWindow6B3FourthMoment_closed (x y z : ℤ) :
    xiWindow6B3FourthMoment x y z =
      10 * (x ^ 4 + y ^ 4 + z ^ 4) + 24 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) := by
  simp [xiWindow6B3FourthMoment, xiWindow6B3Roots, xiWindow6B3ShortRoots, xiWindow6ShortRoots,
    xiRootProbe, xiRootX, xiRootY, xiRootZ]
  ring_nf

private theorem xiWindow6C3FourthMoment_closed (x y z : ℤ) :
    xiWindow6C3FourthMoment x y z =
      40 * (x ^ 4 + y ^ 4 + z ^ 4) + 24 * (x ^ 2 * y ^ 2 + x ^ 2 * z ^ 2 + y ^ 2 * z ^ 2) := by
  simp [xiWindow6C3FourthMoment, xiWindow6C3Roots, xiWindow6LongRoots, xiWindow6ShortRoots,
    xiRootProbe, xiRootX, xiRootY, xiRootZ]
  ring_nf

/-- Paper label: `thm:xi-window6-b3c3-tight-frame-fourth-moment-nonsimilarity`. -/
theorem paper_xi_window6_b3c3_tight_frame_fourth_moment_nonsimilarity :
    XiWindow6B3C3TightFrameFourthMomentNonsimilarityStatement := by
  refine ⟨xiWindow6B3QuadraticMoment_closed, xiWindow6C3QuadraticMoment_closed,
    xiWindow6B3FourthMoment_closed, xiWindow6C3FourthMoment_closed, ?_⟩
  intro h
  rcases h with ⟨s, hs, hscale⟩
  have h100 := hscale 1 0 0
  have h110 := hscale 1 1 0
  norm_num [xiWindow6B3FourthMoment_closed, xiWindow6C3FourthMoment_closed] at h100 h110
  nlinarith

end Omega.Zeta
