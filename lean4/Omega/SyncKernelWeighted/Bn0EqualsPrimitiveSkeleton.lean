import Mathlib

namespace Omega.SyncKernelWeighted

/-- The carry-free primitive orbit count read from the skeleton block `A₀`. -/
def primitiveSkeletonOrbitCount (A₀ : ℕ → ℤ) (n : ℕ) : ℤ :=
  A₀ n

/-- A minimal weighted primitive polynomial model in which the `u = 0` coefficient is exactly the
carry-free primitive skeleton count and the higher-order term records carry-contributing orbits. -/
noncomputable def weightedPrimitivePolynomialAt (A₀ carry : ℕ → ℤ) (n : ℕ) : Polynomial ℤ :=
  Polynomial.C (primitiveSkeletonOrbitCount A₀ n) + Polynomial.C (carry n) * Polynomial.X

/-- Paper label: `cor:Bn0-equals-primitive-skeleton`.
Specializing the weighted primitive polynomial at `u = 0` removes the carry term and leaves exactly
the carry-free skeleton primitive orbit count. -/
theorem paper_Bn0_equals_primitive_skeleton (A₀ carry : ℕ → ℤ) (n : ℕ) :
    (weightedPrimitivePolynomialAt A₀ carry n).eval 0 = primitiveSkeletonOrbitCount A₀ n := by
  simp [weightedPrimitivePolynomialAt, primitiveSkeletonOrbitCount]

end Omega.SyncKernelWeighted
