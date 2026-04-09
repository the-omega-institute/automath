import Mathlib.Tactic

/-!
# Local alphabet budget and Smith prefix nonexchangeability seed values

Power-of-two vs power-of-ten comparisons and gap identities.
-/

namespace Omega.Conclusion

/-- Local alphabet Smith prefix nonexchangeability seeds.
    thm:conclusion-local-alphabet-budget-smith-prefix-budget-nonexchangeability -/
theorem paper_conclusion_local_alphabet_smith_prefix_nonexchangeability_seeds :
    (2 < 10) ∧
    (2 ^ 3 = 8 ∧ 10 ^ 3 = 1000) ∧
    (8 < 1000) ∧
    (2 ^ 9 = 512 ∧ 512 < 1000 ∧ 1000 < 1024 ∧ 2 ^ 10 = 1024) ∧
    (1024 - 1000 = 24) := by
  refine ⟨by omega, ⟨by norm_num, by norm_num⟩, by omega,
         ⟨by norm_num, by omega, by omega, by norm_num⟩, by omega⟩

end Omega.Conclusion
