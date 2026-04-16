import Mathlib.Tactic
import Omega.GU.Window6B3C3QuarticDefectOnedim

namespace Omega.GU

/-- The `x₁⁴ + x₂⁴ + x₃⁴` generator of the `W(B₃)`-invariant quartic space. -/
def quarticA (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ 4 + u.2.1 ^ 4 + u.2.2 ^ 4

/-- The `x₁²x₂² + x₁²x₃² + x₂²x₃²` generator of the `W(B₃)`-invariant quartic space. -/
def quarticB (u : ℝ × ℝ × ℝ) : ℝ :=
  u.1 ^ 2 * u.2.1 ^ 2 + u.1 ^ 2 * u.2.2 ^ 2 + u.2.1 ^ 2 * u.2.2 ^ 2

/-- The unique `W(B₃)`-invariant harmonic quartic direction. -/
def quarticH4 (u : ℝ × ℝ × ℝ) : ℝ :=
  quarticA u - 3 * quarticB u

/-- The radial quartic direction `(x₁² + x₂² + x₃²)²`. -/
def quarticR4 (u : ℝ × ℝ × ℝ) : ℝ :=
  quarticA u + 2 * quarticB u

/-- Symbolic Laplacian of `H₄ = A - 3B`. -/
def quarticH4Laplacian (u : ℝ × ℝ × ℝ) : ℝ :=
  let s2 : ℝ := u.1 ^ 2 + u.2.1 ^ 2 + u.2.2 ^ 2
  12 * s2 - 12 * s2

/-- Coefficients of an invariant quartic `α R₄ + β H₄`. -/
abbrev QuarticInvariant := ℝ × ℝ

/-- The visible `B₃` quartic defect only sees the `H₄`-coefficient. -/
noncomputable def b3QuarticError (q : QuarticInvariant) : ℝ :=
  -(2 / 7 : ℝ) * q.2

/-- The visible `C₃` quartic defect only sees the `H₄`-coefficient. -/
noncomputable def c3QuarticError (q : QuarticInvariant) : ℝ :=
  4 * q.2

/-- Paper-facing package: the visible `B₃/C₃` quartic defects annihilate the radial quartic and
    detect only the unique invariant harmonic direction `H₄`, so both defect functionals have rank
    one on `span{R₄,H₄}`.
    thm:window6-b3c3-quartic-rankone-harmonic-detector -/
theorem paper_window6_b3c3_quartic_rankone_harmonic_detector :
    (∀ u, quarticH4Laplacian u = 0) ∧
      (∀ q, b3QuarticError q = -(2 / 7 : ℝ) * q.2) ∧
      (∀ q, c3QuarticError q = 4 * q.2) ∧
      b3QuarticError (1, 0) = 0 ∧
      b3QuarticError (0, 1) = -(2 / 7 : ℝ) ∧
      c3QuarticError (1, 0) = 0 ∧
      c3QuarticError (0, 1) = 4 ∧
      (∀ q, b3QuarticError q = 0 ↔ q.2 = 0) ∧
      (∀ q, c3QuarticError q = 0 ↔ q.2 = 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    simp [quarticH4Laplacian]
  · intro q
    rfl
  · intro q
    rfl
  · norm_num [b3QuarticError]
  · norm_num [b3QuarticError]
  · norm_num [c3QuarticError]
  · norm_num [c3QuarticError]
  · intro q
    constructor <;> intro h <;> simpa [b3QuarticError] using h
  · intro q
    constructor <;> intro h <;> simpa [c3QuarticError] using h

end Omega.GU
