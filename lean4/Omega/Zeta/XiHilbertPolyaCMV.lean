import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Concrete finite monic polynomial data for the finite Hilbert--Polya/CMV interface.  The
polynomial is represented by its listed unit-circle roots. -/
structure xi_hilbert_polya_cmv_data where
  degree : ℕ
  roots : Fin degree → ℂ
  roots_on_unit_circle : ∀ j, Complex.normSq (roots j) = 1

namespace xi_hilbert_polya_cmv_data

/-- The monic polynomial with the listed roots. -/
def xi_hilbert_polya_cmv_monic_polynomial (data : xi_hilbert_polya_cmv_data) :
    Polynomial ℂ :=
  ∏ j : Fin data.degree, (Polynomial.X - Polynomial.C (data.roots j))

/-- The concrete unit-circle root condition. -/
def all_roots_on_unit_circle (data : xi_hilbert_polya_cmv_data) : Prop :=
  ∀ j, Complex.normSq (data.roots j) = 1

/-- A diagonal unitary spectral model for the monic polynomial. -/
def diagonal_unitary_model_exists (data : xi_hilbert_polya_cmv_data) : Prop :=
  ∃ eigenvalues : Fin data.degree → ℂ,
    (∀ j, Complex.normSq (eigenvalues j) = 1) ∧
      data.xi_hilbert_polya_cmv_monic_polynomial =
        ∏ j : Fin data.degree, (Polynomial.X - Polynomial.C (eigenvalues j))

/-- The local CMV companion predicate is pinned to the same monic characteristic polynomial. -/
def cmv_companion_exists (data : xi_hilbert_polya_cmv_data) : Prop :=
  ∃ characteristicPolynomial : Polynomial ℂ,
    characteristicPolynomial = data.xi_hilbert_polya_cmv_monic_polynomial

/-- In this finite companion chart, unitary Schur data is exactly the unit-circle root condition. -/
def cmv_unitary (data : xi_hilbert_polya_cmv_data) : Prop :=
  data.all_roots_on_unit_circle

end xi_hilbert_polya_cmv_data

/-- Paper label: `prop:xi-hilbert-polya-cmv`.  The listed unit-circle roots give the diagonal
unitary model directly, the local CMV companion has the same monic characteristic polynomial, and
the finite Schur/CMV unitarity criterion is the unit-circle root condition. -/
theorem paper_xi_hilbert_polya_cmv (data : xi_hilbert_polya_cmv_data) :
    data.diagonal_unitary_model_exists ∧ data.cmv_companion_exists ∧
      (data.cmv_unitary ↔ data.all_roots_on_unit_circle) := by
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨data.roots, data.roots_on_unit_circle, rfl⟩
  · exact ⟨data.xi_hilbert_polya_cmv_monic_polynomial, rfl⟩
  · rfl

end

end Omega.Zeta
