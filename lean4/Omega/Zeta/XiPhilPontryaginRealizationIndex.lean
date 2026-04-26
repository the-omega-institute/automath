import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete data for the Cayley--Schur negative-square index comparison.  The three
natural numbers record, respectively, the Cayley-side kernel index, the Schur-side kernel
index, and the Pontryagin realization index. -/
structure xi_phil_pontryagin_realization_index_data where
  cayleySchurNegativeSquares : ℕ
  schurKernelNegativeSquares : ℕ
  minimalRealizationIndex : ℕ
  pontryaginIndex : ℕ
  kappa : ℕ
  cayley_schur_preserves_negative_squares :
    cayleySchurNegativeSquares = schurKernelNegativeSquares
  minimal_realization_index_eq_negative_squares :
    minimalRealizationIndex = schurKernelNegativeSquares
  pontryagin_index_eq_realization_index :
    pontryaginIndex = minimalRealizationIndex
  schur_negative_squares_eq_kappa :
    schurKernelNegativeSquares = kappa

/-- The Hilbert-space case is the zero-index case for the prefixed package. -/
def xi_phil_pontryagin_realization_index_data.isHilbertCase
    (D : xi_phil_pontryagin_realization_index_data) : Prop :=
  D.kappa = 0

/-- The concrete realization-index conclusion: the Pontryagin index equals the
Cayley-side negative-square count and hence equals `kappa`; in particular the Hilbert
case is exactly the zero-index case. -/
def xi_phil_pontryagin_realization_index_data.statement
    (D : xi_phil_pontryagin_realization_index_data) : Prop :=
  D.pontryaginIndex = D.cayleySchurNegativeSquares ∧
    D.pontryaginIndex = D.kappa ∧
    (D.isHilbertCase ↔ D.pontryaginIndex = 0)

/-- Paper label: `cor:xi-phiL-pontryagin-realization-index`. -/
theorem paper_xi_phil_pontryagin_realization_index
    (D : xi_phil_pontryagin_realization_index_data) : D.statement := by
  have h_to_schur :
      D.pontryaginIndex = D.schurKernelNegativeSquares := by
    calc
      D.pontryaginIndex = D.minimalRealizationIndex :=
        D.pontryagin_index_eq_realization_index
      _ = D.schurKernelNegativeSquares :=
        D.minimal_realization_index_eq_negative_squares
  have h_to_cayley :
      D.pontryaginIndex = D.cayleySchurNegativeSquares := by
    calc
      D.pontryaginIndex = D.schurKernelNegativeSquares := h_to_schur
      _ = D.cayleySchurNegativeSquares :=
        D.cayley_schur_preserves_negative_squares.symm
  have h_to_kappa : D.pontryaginIndex = D.kappa := by
    exact h_to_schur.trans D.schur_negative_squares_eq_kappa
  refine ⟨h_to_cayley, h_to_kappa, ?_⟩
  constructor
  · intro hHilbert
    exact h_to_kappa.trans hHilbert
  · intro hZero
    exact h_to_kappa.symm.trans hZero

end Omega.Zeta
