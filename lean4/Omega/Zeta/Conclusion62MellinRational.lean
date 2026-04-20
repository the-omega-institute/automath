import Mathlib

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The golden ratio, used to pass from `s` to the Mellin variable `z = φ^{-s}`. -/
def conclusion62Phi : ℂ :=
  ((1 + Real.sqrt 5) / 2 : ℝ)

/-- The Mellin variable `z = φ^{-s}` in exponential form. -/
def conclusion62Z (s : ℂ) : ℂ :=
  Complex.exp (-s * Complex.log conclusion62Phi)

/-- The diagonal finite-state system matrix `I - A(z)` controlling the restricted Mellin moments. -/
def conclusion62SystemMatrix {d : ℕ} (a : Fin d → ℂ) (s : ℂ) : Matrix (Fin d) (Fin d) ℂ :=
  Matrix.diagonal fun i => 1 - a i * conclusion62Z s

/-- The restricted Mellin moments packaged as a finite vector. -/
def conclusion62MomentVector {d : ℕ} (w a : Fin d → ℂ) (s : ℂ) : Fin d → ℂ :=
  fun i => w i / (1 - a i * conclusion62Z s)

/-- The polynomial denominator controlling the Mellin poles. -/
def conclusion62PolePolynomial {d : ℕ} (a : Fin d → ℂ) (s : ℂ) : ℂ :=
  ∏ i, (1 - a i * conclusion62Z s)

/-- Paper label: `thm:conclusion62-mellin-rational`. For the diagonal finite-state refinement
model, the restricted Mellin vector solves `(I - A(z)) M = b` whenever the diagonal factors are
nonzero, and the pole set is contained in the zero set of `det (I - A(z))`. -/
theorem paper_conclusion62_mellin_rational (d : ℕ) (w a : Fin d → ℂ) :
    (∀ s, (∀ i, 1 - a i * conclusion62Z s ≠ 0) →
      Matrix.mulVec (conclusion62SystemMatrix a s) (conclusion62MomentVector w a s) = w) ∧
    (∀ s, Matrix.det (conclusion62SystemMatrix a s) = conclusion62PolePolynomial a s) ∧
    (∀ s i, 1 - a i * conclusion62Z s ≠ 0 →
      (1 - a i * conclusion62Z s) * conclusion62MomentVector w a s i = w i) := by
  refine ⟨?_, ?_, ?_⟩
  · intro s hs
    ext i
    rw [conclusion62SystemMatrix, Matrix.mulVec_diagonal]
    rw [conclusion62MomentVector, div_eq_mul_inv]
    calc
      (1 - a i * conclusion62Z s) * (w i * (1 - a i * conclusion62Z s)⁻¹)
          = w i * ((1 - a i * conclusion62Z s) * (1 - a i * conclusion62Z s)⁻¹) := by
            ac_rfl
      _ = w i := by simp [hs i]
  · intro s
    simp [conclusion62SystemMatrix, conclusion62PolePolynomial]
  · intro s i hi
    rw [conclusion62MomentVector, div_eq_mul_inv]
    calc
      (1 - a i * conclusion62Z s) * (w i * (1 - a i * conclusion62Z s)⁻¹)
          = w i * ((1 - a i * conclusion62Z s) * (1 - a i * conclusion62Z s)⁻¹) := by
            ac_rfl
      _ = w i := by simp [hi]

end

end Omega.Zeta
