import Mathlib

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- A finite prime-support scalar model for the Witt-depth Euler product. The local factors are
geometric sums over the prime powers retained at each prime, and the "translation operators" are
represented by the scalar weights `translation (p^k)`. -/
structure WittDepthEulerProductData where
  primeSupport : Finset ℕ
  depth : ℕ → ℕ
  translation : ℕ → ℚ
  localWeight : ℕ → ℕ → ℚ

namespace WittDepthEulerProductData

/-- The prime-local geometric-series factor at `p`. -/
def primeLocalFactor (D : WittDepthEulerProductData) (p : ℕ) : ℚ :=
  Finset.sum (Finset.range (D.depth p + 1)) fun k =>
    D.localWeight p k * D.translation (p ^ k)

/-- The finite-depth regularized Witt operator obtained by multiplying the local prime factors in
the chosen support. -/
def regularizedWittOperatorAux (D : WittDepthEulerProductData) (s : Finset ℕ) : ℚ :=
  Finset.prod s D.primeLocalFactor

/-- The full finite Euler product over the chosen prime support. -/
def regularizedWittOperator (D : WittDepthEulerProductData) : ℚ :=
  D.regularizedWittOperatorAux D.primeSupport

/-- Every prime-local factor is the advertised geometric sum, and the regularized operator is the
Euler product of those local factors. -/
def Holds (D : WittDepthEulerProductData) : Prop :=
  (∀ p ∈ D.primeSupport,
      D.primeLocalFactor p =
        Finset.sum (Finset.range (D.depth p + 1)) fun k =>
          D.localWeight p k * D.translation (p ^ k)) ∧
    D.regularizedWittOperator = Finset.prod D.primeSupport D.primeLocalFactor

lemma regularizedWittOperatorAux_eq_prod (D : WittDepthEulerProductData) (s : Finset ℕ) :
    D.regularizedWittOperatorAux s = Finset.prod s D.primeLocalFactor := by
  rfl

end WittDepthEulerProductData

/-- Paper label: `thm:witt-depth-euler-product`.
In the finite scalar translation model, each prime-local factor is the expected geometric series,
and the truncated regularized Witt operator is exactly the Euler product of those local factors. -/
theorem paper_witt_depth_euler_product (D : WittDepthEulerProductData) : D.Holds := by
  refine ⟨?_, ?_⟩
  · intro p hp
    rfl
  · simpa [WittDepthEulerProductData.regularizedWittOperator] using
      D.regularizedWittOperatorAux_eq_prod D.primeSupport

end Omega.SyncKernelWeighted
