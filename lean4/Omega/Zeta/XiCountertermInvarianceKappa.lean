import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Concrete finite-window data for a Toeplitz block and a pure imaginary constant
counterterm.  The invariant is kept as a concrete function of the Hermitianized block. -/
structure xi_counterterm_invariance_kappa_data where
  N : ℕ
  coeff : ℤ → ℂ
  eta : ℝ
  kappa : Matrix (Fin (N + 1)) (Fin (N + 1)) ℂ → ℕ

/-- Add the pure imaginary constant counterterm to the zeroth coefficient. -/
noncomputable def xi_counterterm_invariance_kappa_shiftedCoeff
    (D : xi_counterterm_invariance_kappa_data) (n : ℤ) : ℂ :=
  if n = 0 then D.coeff 0 + (D.eta : ℂ) * Complex.I else D.coeff n

/-- Hermitianization of the Toeplitz coefficient sequence.  At the constant coefficient only
the real part contributes, so a pure imaginary counterterm is invisible. -/
noncomputable def xi_counterterm_invariance_kappa_hermitianCoeff
    (c : ℤ → ℂ) (n : ℤ) : ℂ :=
  if n = 0 then ((c 0).re : ℂ) else c n

/-- The Hermitianized Toeplitz block before the counterterm. -/
noncomputable def xi_counterterm_invariance_kappa_blockBefore
    (D : xi_counterterm_invariance_kappa_data) :
    Matrix (Fin (D.N + 1)) (Fin (D.N + 1)) ℂ :=
  fun i j =>
    xi_counterterm_invariance_kappa_hermitianCoeff D.coeff ((i : ℤ) - (j : ℤ))

/-- The Hermitianized Toeplitz block after the counterterm. -/
noncomputable def xi_counterterm_invariance_kappa_blockAfter
    (D : xi_counterterm_invariance_kappa_data) :
    Matrix (Fin (D.N + 1)) (Fin (D.N + 1)) ℂ :=
  fun i j =>
    xi_counterterm_invariance_kappa_hermitianCoeff
      (xi_counterterm_invariance_kappa_shiftedCoeff D) ((i : ℤ) - (j : ℤ))

/-- The negative-inertia/kappa invariant read from the finite Hermitianized block. -/
noncomputable def xi_counterterm_invariance_kappa_value
    (D : xi_counterterm_invariance_kappa_data)
    (M : Matrix (Fin (D.N + 1)) (Fin (D.N + 1)) ℂ) : ℕ :=
  D.kappa M

/-- Pure imaginary constant counterterms do not change the Hermitianized Toeplitz block or
any invariant that is a function of that block. -/
def xi_counterterm_invariance_kappa_statement
    (D : xi_counterterm_invariance_kappa_data) : Prop :=
  xi_counterterm_invariance_kappa_blockAfter D =
      xi_counterterm_invariance_kappa_blockBefore D ∧
    xi_counterterm_invariance_kappa_value D
        (xi_counterterm_invariance_kappa_blockAfter D) =
      xi_counterterm_invariance_kappa_value D
        (xi_counterterm_invariance_kappa_blockBefore D)

/-- Paper label: `thm:xi-counterterm-invariance-kappa`. -/
theorem paper_xi_counterterm_invariance_kappa
    (D : xi_counterterm_invariance_kappa_data) :
    xi_counterterm_invariance_kappa_statement D := by
  have hblock :
      xi_counterterm_invariance_kappa_blockAfter D =
        xi_counterterm_invariance_kappa_blockBefore D := by
    ext i j
    by_cases h : (i : ℤ) - (j : ℤ) = 0
    · simp [xi_counterterm_invariance_kappa_blockAfter,
        xi_counterterm_invariance_kappa_blockBefore,
        xi_counterterm_invariance_kappa_hermitianCoeff,
        xi_counterterm_invariance_kappa_shiftedCoeff, h]
    · simp [xi_counterterm_invariance_kappa_blockAfter,
        xi_counterterm_invariance_kappa_blockBefore,
        xi_counterterm_invariance_kappa_hermitianCoeff,
        xi_counterterm_invariance_kappa_shiftedCoeff, h]
  exact ⟨hblock, congrArg (xi_counterterm_invariance_kappa_value D) hblock⟩

end Omega.Zeta
