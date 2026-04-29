import Omega.Zeta.SmithEntropyMinDepth

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-smith-loss-euler-atomic-decomposition`. -/
theorem paper_conclusion_smith_loss_euler_atomic_decomposition (s t : Multiset ℕ) :
    (∀ k : ℕ, Omega.Zeta.smithEntropy s k = (s.map fun e => min k e).sum) ∧
      (∀ k : ℕ,
        Omega.Zeta.smithEntropy (s + t) k =
          Omega.Zeta.smithEntropy s k + Omega.Zeta.smithEntropy t k) := by
  constructor
  · intro k
    simp [Omega.Zeta.smithEntropy, Nat.min_comm]
  · intro k
    simp [Omega.Zeta.smithEntropy, Multiset.map_add, Multiset.sum_add]

end Omega.Conclusion
