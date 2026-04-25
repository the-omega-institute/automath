import Mathlib.Tactic
import Omega.Folding.FiberWeightCount

namespace Omega.POM

/-- Paper label: `prop:pom-hiddenbit-mixed-moment-cluster`. The `k`-th power sum of the fiber
multiplicity field splits by the hidden-bit decomposition `d(x) = d₀(x) + d₁(x)`, and the
binomial expansion can be interchanged with the finite sum over stable residues. -/
theorem paper_pom_hiddenbit_mixed_moment_cluster (k m : ℕ) :
    momentSum k m = Finset.sum (Finset.range (k + 1)) (fun a =>
      Nat.choose k a * (∑ x : X m, fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
  calc
    momentSum k m
        = ∑ x : X m, X.fiberMultiplicity x ^ k := rfl
    _ = ∑ x : X m, Finset.sum (Finset.range (k + 1)) (fun a =>
          Nat.choose k a *
            (fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
          refine Finset.sum_congr rfl ?_
          intro x _
          rw [fiberMultiplicity_split_by_hiddenBit x]
          simpa [mul_assoc, mul_left_comm, mul_comm] using
            (add_pow (fiberHiddenBitCount 0 x) (fiberHiddenBitCount 1 x) k)
    _ = Finset.sum (Finset.range (k + 1)) (fun a => ∑ x : X m,
          Nat.choose k a *
            (fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
          rw [Finset.sum_comm]
    _ = Finset.sum (Finset.range (k + 1)) (fun a => Nat.choose k a *
          (∑ x : X m, fiberHiddenBitCount 0 x ^ a * fiberHiddenBitCount 1 x ^ (k - a))) := by
          refine Finset.sum_congr rfl ?_
          intro a _
          rw [← Finset.mul_sum]

end Omega.POM
