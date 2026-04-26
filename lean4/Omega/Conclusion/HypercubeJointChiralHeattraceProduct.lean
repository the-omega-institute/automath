import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-hypercube-joint-chiral-heattrace-product`. The replicated
local heat-trace factors multiply to the corresponding powers. -/
theorem paper_conclusion_hypercube_joint_chiral_heattrace_product (q : ℝ)
    (free nPlus nMinus : ℕ) :
    (List.replicate nMinus q).prod * (List.replicate nPlus (1 + q + q ^ 2)).prod *
        (List.replicate free (1 + q)).prod =
      q ^ nMinus * (1 + q + q ^ 2) ^ nPlus * (1 + q) ^ free := by
  simp [List.prod_replicate]

end Omega.Conclusion
