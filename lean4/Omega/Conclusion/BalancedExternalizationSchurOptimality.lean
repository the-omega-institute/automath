import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTimePart64baFoldMultiplicityMajorizationBalancing

namespace Omega.Conclusion

open Matrix

/-- Paper label: `thm:conclusion-balanced-externalization-schur-optimality`.
The conclusion-level balanced externalization packages the local Robin-Hood transfer certificate,
the two-level balanced occupancy profile, and the identity doubly stochastic witness coming from
the already formalized fold-multiplicity balancing theorem. -/
theorem paper_conclusion_balanced_externalization_schur_optimality {F M : ℕ} :
    let b := Omega.Zeta.xiTimePart64baBalancedProfile F M
    (∀ x y : ℤ, y + 2 ≤ x →
      (x - 1) + (y + 1) = x + y ∧ (x - 1) ^ 2 + (y + 1) ^ 2 < x ^ 2 + y ^ 2) ∧
      (∀ i, b i = M / F ∨ b i = M / F + 1) ∧
      (∀ i j, Int.natAbs ((b i : ℤ) - b j) ≤ 1) ∧
      Omega.Zeta.xiTimePart64baDoublyStochastic (1 : Matrix (Fin F) (Fin F) ℚ) ∧
      (Matrix.mulVec (1 : Matrix (Fin F) (Fin F) ℚ) (fun i => (b i : ℚ)) = fun i => (b i : ℚ)) := by
  simpa using
    (Omega.Zeta.paper_xi_time_part64ba_fold_multiplicity_majorization_balancing
      (F := F) (M := M))

end Omega.Conclusion
