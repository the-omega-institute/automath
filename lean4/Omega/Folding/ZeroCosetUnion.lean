import Omega.Core.Fib
import Omega.Folding.FiberConvolutionKernelZeroSpectrum

namespace Omega.Folding

/-- Paper label: `cor:fold-zero-coset-union`. The fold-kernel zero set at Fibonacci modulus is
the union of the singleton zero spectra, and the associated gcd labels are given pointwise by the
standard Fibonacci gcd identity. -/
theorem paper_fold_zero_coset_union (m : ℕ) :
    foldFiberConvolutionKernelZeroSet (Nat.fib (m + 2)) (Finset.range m) =
        (Finset.range m).biUnion (foldFiberSingletonZeroSet (Nat.fib (m + 2))) ∧
      ∀ j ∈ Finset.range m,
        Nat.gcd (Nat.fib (j + 1)) (Nat.fib (m + 2)) = Nat.fib (Nat.gcd (j + 1) (m + 2)) := by
  refine ⟨?_, ?_⟩
  · exact
      (paper_fold_fiber_convolution_kernel_zero_spectrum
        (Nat.fib (m + 2)) (Finset.range m)).1
  · intro j hj
    let _ := hj
    simpa using (Omega.fib_gcd (j + 1) (m + 2))

end Omega.Folding
