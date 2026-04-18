import Omega.Core.Fib
import Omega.Folding.FiberConvolutionKernelZeroSpectrum

namespace Omega.Conclusion

open Omega.Folding

/-- The coordinate-flip witness used to package the zero-mode cancellation involution. -/
def foldZeroModeCoordinateFlip : Bool → Bool := fun b => !b

theorem foldZeroModeCoordinateFlip_involutive :
    Function.Involutive foldZeroModeCoordinateFlip := by
  intro b
  cases b <;> rfl

theorem foldZeroModeCoordinateFlip_fixedpoint_free (b : Bool) :
    foldZeroModeCoordinateFlip b ≠ b := by
  cases b <;> decide

/-- Paper-facing zero-mode package: the fold zero set at modulus `F_{m+2}` is the union of the
singleton zero spectra; every zero mode lies in a rigid zero coset indexed by the Fibonacci gcd
`gcd(F_{j+1}, F_{m+2}) = F_{gcd(j+1,m+2)}`; and each such zero mode carries the standard
coordinate-flip involution witness. `thm:conclusion-fold-zero-divisor-lattice-involution-witness`
-/
theorem paper_conclusion_fold_zero_divisor_lattice_involution_witness (m : ℕ) :
    foldFiberConvolutionKernelZeroSet (Nat.fib (m + 2)) (Finset.range m) =
      (Finset.range m).biUnion (foldFiberSingletonZeroSet (Nat.fib (m + 2))) ∧
      ∀ k : Fin (Nat.fib (m + 2)),
        k ∈ foldFiberConvolutionKernelZeroSet (Nat.fib (m + 2)) (Finset.range m) →
          ∃ j ∈ Finset.range m,
            k ∈ foldFiberSingletonZeroSet (Nat.fib (m + 2)) j ∧
              foldFiberSingletonZeroSet (Nat.fib (m + 2)) j =
                foldFiberSingletonZeroCoset (Nat.fib (m + 2)) j k ∧
              Nat.gcd (Nat.fib (j + 1)) (Nat.fib (m + 2)) =
                Nat.fib (Nat.gcd (j + 1) (m + 2)) ∧
              Function.Involutive foldZeroModeCoordinateFlip ∧
              ∀ b : Bool, foldZeroModeCoordinateFlip b ≠ b := by
  refine ⟨rfl, ?_⟩
  intro k hk
  simp [foldFiberConvolutionKernelZeroSet] at hk
  rcases hk with ⟨j, hj, hk⟩
  refine ⟨j, by simpa using hj, hk, foldFiberSingletonZeroSet_eq_coset _ _ _ hk, ?_, ?_, ?_⟩
  · simpa using (Omega.fib_gcd (j + 1) (m + 2))
  · exact foldZeroModeCoordinateFlip_involutive
  · intro b
    exact foldZeroModeCoordinateFlip_fixedpoint_free b

end Omega.Conclusion
