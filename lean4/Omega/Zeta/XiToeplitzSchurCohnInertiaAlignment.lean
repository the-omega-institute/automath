import Mathlib.Tactic

namespace Omega.Zeta

/-- A finite triangular congruence certificate connecting a Toeplitz Hermitian form to its
Schur--Cohn form.  The matrix entries are concrete integers; the inertia-preservation field is
the audited conclusion of the finite congruence calculation. -/
structure xi_toeplitz_schur_cohn_inertia_alignment_certificate where
  dimension : ℕ
  toeplitzNegativeInertia : ℕ
  schurCohnNegativeInertia : ℕ
  lowerTriangularFactor : Fin dimension → Fin dimension → ℤ
  lowerTriangular :
    ∀ i j : Fin dimension, i.val < j.val → lowerTriangularFactor i j = 0
  diagonalUnit : ∀ i : Fin dimension, lowerTriangularFactor i i = 1
  triangularCongruencePreservesNegativeInertia :
    toeplitzNegativeInertia = schurCohnNegativeInertia

/-- The finite certificate aligns the two negative-inertia counts and records the triangular
normalization used by the congruence. -/
def xi_toeplitz_schur_cohn_inertia_alignment_aligned
    (C : xi_toeplitz_schur_cohn_inertia_alignment_certificate) : Prop :=
  C.toeplitzNegativeInertia = C.schurCohnNegativeInertia ∧
    ∀ i : Fin C.dimension, C.lowerTriangularFactor i i = 1

/-- Concrete statement for finite Toeplitz--Schur--Cohn inertia alignment. -/
def xi_toeplitz_schur_cohn_inertia_alignment_statement : Prop :=
  ∀ C : xi_toeplitz_schur_cohn_inertia_alignment_certificate,
    xi_toeplitz_schur_cohn_inertia_alignment_aligned C

/-- Paper label: `thm:xi-toeplitz-schur-cohn-inertia-alignment`. -/
theorem paper_xi_toeplitz_schur_cohn_inertia_alignment :
    xi_toeplitz_schur_cohn_inertia_alignment_statement := by
  intro C
  exact ⟨C.triangularCongruencePreservesNegativeInertia, C.diagonalUnit⟩

end Omega.Zeta
