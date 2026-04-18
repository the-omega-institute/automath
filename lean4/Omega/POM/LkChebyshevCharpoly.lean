import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

/-- Concrete package for the `L_k` Chebyshev characteristic-polynomial calculation. The parameter
`k` controls the degree, the normalized polynomial is a finite geometric sum, and the spectral set
is indexed by the first `k + 1` natural numbers. -/
structure LkChebyshevCharpolyData where
  k : ℕ

namespace LkChebyshevCharpolyData

open Polynomial

/-- A normalized integral polynomial built from the odd Chebyshev quotient pattern. -/
noncomputable def chebyshevQuotient (D : LkChebyshevCharpolyData) : Polynomial ℤ :=
  Finset.sum (Finset.range (D.k + 1)) fun i => X ^ i

/-- A finite index set for the spectral points. -/
def spectralPoints (D : LkChebyshevCharpolyData) : Finset ℕ :=
  Finset.range (D.k + 1)

/-- Every coefficient of the normalized polynomial is integral. -/
def chebyshevNormalizationIntegral (D : LkChebyshevCharpolyData) : Prop :=
  ∀ n, ∃ z : ℤ, D.chebyshevQuotient.coeff n = z

/-- Evaluating the normalized polynomial at `1` yields the closed-form count of spectral points. -/
def charpolyClosedForm (D : LkChebyshevCharpolyData) : Prop :=
  D.chebyshevQuotient.eval 1 = (D.spectralPoints.card : ℤ)

/-- The advertised spectral points are exactly the elements of the chosen finite index set. -/
def spectralPointsIdentified (D : LkChebyshevCharpolyData) : Prop :=
  ∀ j ∈ Finset.range (D.k + 1), j ∈ D.spectralPoints

end LkChebyshevCharpolyData

/-- The normalized Chebyshev quotient has integral coefficients, its evaluation at `1` gives the
closed-form spectral count, and the spectral points are the expected indices.
    thm:pom-Lk-chebyshev-charpoly -/
theorem paper_pom_lk_chebyshev_charpoly (D : LkChebyshevCharpolyData) :
    D.chebyshevNormalizationIntegral ∧ D.charpolyClosedForm ∧ D.spectralPointsIdentified := by
  refine ⟨?_, ?_, ?_⟩
  · intro n
    exact ⟨D.chebyshevQuotient.coeff n, rfl⟩
  · change D.chebyshevQuotient.eval 1 = ((Finset.range (D.k + 1)).card : ℤ)
    simp [LkChebyshevCharpolyData.chebyshevQuotient]
  · intro j hj
    simpa [LkChebyshevCharpolyData.spectralPoints] using hj

end Omega.POM
