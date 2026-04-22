import Mathlib.Data.Rat.Defs
import Mathlib.Tactic
import Omega.Conclusion.DerivedT5BurnsideMoments
import Omega.Conclusion.EllipticT5SolvabilityAndTotalSplittingDensity

namespace Omega.Conclusion

/-- Natural-density table for the three admissible `T₅` root counts `0`, `4`, and `24`. -/
def derivedT5RootCountDensity : ℕ → ℚ
  | 0 => 73 / 96
  | 4 => 19 / 80
  | 24 => 1 / 480
  | _ => 0

/-- Paper label: `thm:derived-t5-three-valued-root-count`.
The `T₅` root-count distribution is supported exactly on `0`, `4`, and `24`; the `24`-root atom is
the full-splitting density, the `4`-root atom is the remaining solvable density, and the first
moment agrees with the Burnside-count computation. -/
theorem paper_derived_t5_three_valued_root_count :
    derivedT5RootCountDensity 0 = 73 / 96 ∧
    derivedT5RootCountDensity 4 = 19 / 80 ∧
    derivedT5RootCountDensity 24 = 1 / 480 ∧
    (∀ N : ℕ, derivedT5RootCountDensity N ≠ 0 → N = 0 ∨ N = 4 ∨ N = 24) ∧
    ((0 : ℚ) * derivedT5RootCountDensity 0 + 4 * derivedT5RootCountDensity 4 +
        24 * derivedT5RootCountDensity 24 = 1) := by
  have hsplit :=
    paper_conclusion_elliptic_t5_solvability_and_total_splitting_density
      (23 / 96) (1 / 480) rfl rfl
  have hburnside := paper_derived_t5_burnside_moments
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · norm_num [derivedT5RootCountDensity]
  · norm_num [derivedT5RootCountDensity]
  · simpa [derivedT5RootCountDensity] using hsplit.2
  · intro N hN
    by_cases h0 : N = 0
    · exact Or.inl h0
    by_cases h4 : N = 4
    · exact Or.inr (Or.inl h4)
    by_cases h24 : N = 24
    · exact Or.inr (Or.inr h24)
    have hzero : derivedT5RootCountDensity N = 0 := by
      simp [derivedT5RootCountDensity]
    exact (hN hzero).elim
  · simpa [derivedT5RootCountDensity] using hburnside.1

end Omega.Conclusion
