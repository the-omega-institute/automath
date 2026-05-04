import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-leyang-cubic-chebotarev-splitting-densities`. -/
theorem paper_conclusion_leyang_cubic_chebotarev_splitting_densities
    (split transitive irreducible rootDensity : ℚ) (hsplit : split = 1 / 6)
    (htransitive : transitive = 1 / 2) (hirreducible : irreducible = 1 / 3)
    (hroot : rootDensity = split + transitive) :
    split = 1 / 6 ∧ transitive = 1 / 2 ∧ irreducible = 1 / 3 ∧
      rootDensity = 2 / 3 := by
  refine ⟨hsplit, htransitive, hirreducible, ?_⟩
  calc
    rootDensity = split + transitive := hroot
    _ = 1 / 6 + 1 / 2 := by rw [hsplit, htransitive]
    _ = 2 / 3 := by norm_num

end Omega.Conclusion
