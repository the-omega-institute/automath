import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hypercube-pairwise-cyclotomic-quantization`. -/
theorem paper_conclusion_hypercube_pairwise_cyclotomic_quantization
    (m r nPlus nMinus q Z Zneg : Nat) (hSplit : nMinus + nPlus = r)
    (hZ : Z = q ^ nMinus * (1 + q + q ^ 2) ^ nPlus * (1 + q) ^ (m - 2 * r))
    (hZneg : Zneg = q ^ r * (1 + q) ^ (m - 2 * r)) :
    Z * q ^ nPlus = Zneg * (1 + q + q ^ 2) ^ nPlus := by
  subst Z
  subst Zneg
  subst r
  rw [pow_add]
  ring

end Omega.Conclusion
