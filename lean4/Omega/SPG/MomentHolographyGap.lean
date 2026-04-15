import Mathlib.Tactic

/-!
# Single-integer vs linear moment holography gap seed values

Power-of-two cardinalities, logarithm values, and gap inequalities.
-/

namespace Omega.SPG

/-- Single-integer vs linear moment holography gap seeds.
    thm:spg-single-integer-vs-linear-moment-holography-gap -/
theorem paper_spg_single_integer_vs_linear_moment_gap_seeds :
    (1 < 2 ^ (1 * 1) ∧ 1 < 2 ^ (2 * 1) ∧ 1 < 2 ^ (1 * 2)) ∧
    (2 ^ 1 = 2 ∧ 2 ^ 2 = 4 ∧ 2 ^ 3 = 8 ∧ 2 ^ 4 = 16) ∧
    (2 ^ (2 * 3) = 64) ∧
    (Nat.log 2 4 = 2 ∧ Nat.log 2 8 = 3 ∧ Nat.log 2 16 = 4) := by
  refine ⟨⟨by norm_num, by norm_num, by norm_num⟩,
         ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩,
         by norm_num,
         ⟨by native_decide, by native_decide, by native_decide⟩⟩

/-- Linear moment holography minimal dimension seeds.
    thm:spg-linear-moment-holography-minimal-dimension -/
theorem paper_spg_linear_moment_holography_minimal_dim_seeds :
    (2 ^ (1 * 1) = 2 ∧ 2 ^ (1 * 2) = 4 ∧ 2 ^ (2 * 2) = 16) ∧
    (∀ N L : Nat, L < N → 0 < N - L) ∧
    (2 ^ (2 * 1) = 4 ∧ 2 ^ (2 * 2) = 16 ∧ 2 ^ (2 * 3) = 64) ∧
    (2 ^ 3 = 8 ∧ 2 ^ 6 = 64 ∧ 8 < 64) := by
  exact ⟨⟨by norm_num, by norm_num, by norm_num⟩, fun _ _ h => by omega,
         ⟨by norm_num, by norm_num, by norm_num⟩,
         ⟨by norm_num, by norm_num, by omega⟩⟩

end Omega.SPG
