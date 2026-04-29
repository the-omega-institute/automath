import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Paper label: `cor:conclusion-coordinate-bundle-face-shapley-banzhaf`. -/
theorem paper_conclusion_coordinate_bundle_face_shapley_banzhaf (k : ℕ) (hk : 0 < k) :
    ∃ shapley banzhaf : Fin k → ℚ,
      (∀ e, shapley e = 1 / (k : ℚ)) ∧
        (∀ e, banzhaf e = 1 / (2 : ℚ) ^ (k - 1)) ∧
          (∑ e : Fin k, shapley e) = 1 := by
  classical
  refine ⟨fun _ => 1 / (k : ℚ), fun _ => 1 / (2 : ℚ) ^ (k - 1), ?_, ?_, ?_⟩
  · intro e
    rfl
  · intro e
    rfl
  · simp [Finset.sum_const, Fintype.card_fin, hk.ne']

end Omega.Conclusion
