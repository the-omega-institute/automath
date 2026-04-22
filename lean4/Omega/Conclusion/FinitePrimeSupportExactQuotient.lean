import Omega.CircleDimension.FinitePrimeTruncationKernels

namespace Omega.Conclusion

/-- Paper-facing exact quotient for finite prime support: the restriction map from the larger
finite-prime truncation `T` to the smaller truncation `S` is surjective, and its kernel is exactly
the product of the `p`-adic axes added in `T \ S`.
    thm:conclusion-finite-primesupport-exact-quotient -/
theorem paper_conclusion_finite_primesupport_exact_quotient {S T : Finset ℕ} (hST : S ⊆ T) :
    Function.Surjective (Omega.CircleDimension.finitePrimeTruncationMap hST) ∧
      Nonempty
        (Omega.CircleDimension.FinitePrimeTruncationKernel hST ≃
          Omega.CircleDimension.AddedPrimeProduct S T) := by
  exact ⟨Omega.CircleDimension.finitePrimeTruncationMap_surjective hST,
    ⟨Omega.CircleDimension.finitePrimeTruncationKernelEquivAddedPrimeProduct hST⟩⟩

end Omega.Conclusion
