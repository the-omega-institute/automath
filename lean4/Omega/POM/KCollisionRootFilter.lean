import Mathlib.Tactic

/-!
# K-collision root-of-unity filter recurrence seed values

Binomial coefficient values, integer division, and sign powers
for the root-of-unity filter partition function.
-/

namespace Omega.POM

/-- K-collision root filter recurrence seeds.
    thm:pom-kcollision-root-filter-recurrence -/
theorem paper_pom_kcollision_root_filter_recurrence_seeds :
    (Nat.choose 2 0 = 1 ∧ Nat.choose 2 1 = 2 ∧ Nat.choose 2 2 = 1) ∧
    (Nat.choose 1 1 = 1 ∧ Nat.choose 2 1 = 2) ∧
    (Nat.choose 3 1 = 3 ∧ Nat.choose 3 2 = 3 ∧ Nat.choose 3 3 = 1) ∧
    (Nat.choose 2 2 = 1 ∧ Nat.choose 3 2 = 3 ∧ Nat.choose 4 2 = 6) ∧
    (4 / 2 = 2 ∧ 5 / 3 = 1) ∧
    ((-1 : ℤ) ^ 2 = 1 ∧ (-1 : ℤ) ^ 3 = -1) := by
  exact ⟨⟨by decide, by decide, by decide⟩,
         ⟨by decide, by decide⟩,
         ⟨by decide, by decide, by decide⟩,
         ⟨by decide, by decide, by decide⟩,
         ⟨by omega, by omega⟩,
         ⟨by norm_num, by norm_num⟩⟩

end Omega.POM
