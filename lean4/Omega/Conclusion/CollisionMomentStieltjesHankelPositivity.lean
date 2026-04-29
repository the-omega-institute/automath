import Mathlib.Tactic
import Omega.Folding.MomentTriple

namespace Omega.Conclusion

/-- The adjacent `2 × 2` Hankel principal minor of the collision moment sequence. -/
noncomputable def collisionMomentAdjacentHankelMinor (m q : ℕ) : ℤ :=
  (Omega.momentSum q m : ℤ) * Omega.momentSum (q + 2) m - (Omega.momentSum (q + 1) m : ℤ) ^ 2

/-- Every adjacent Hankel principal minor is nonnegative. -/
noncomputable def collisionMomentHankelPrincipalMinorsNonneg (m : ℕ) : Prop :=
  ∀ q : ℕ, 0 ≤ collisionMomentAdjacentHankelMinor m q

/-- The fixed-resolution collision moments form a log-convex sequence in the moment index. -/
noncomputable def collisionMomentAdjacentMomentsLogConvex (m : ℕ) : Prop :=
  ∀ q : ℕ, Omega.momentSum (q + 1) m ^ 2 ≤ Omega.momentSum q m * Omega.momentSum (q + 2) m

/-- The successive ratio sequence `S_{q+1}(m) / S_q(m)` is monotone. -/
noncomputable def collisionMomentSuccessiveRatioMonotone (m : ℕ) : Prop :=
  ∀ q : ℕ,
    (Omega.momentSum (q + 1) m : ℚ) / Omega.momentSum q m ≤
      (Omega.momentSum (q + 2) m : ℚ) / Omega.momentSum (q + 1) m

/-- Paper-facing Stieltjes/Hankel positivity package for the fixed-resolution collision moments:
the adjacent Hankel minors are nonnegative, hence the moments are log-convex and the successive
ratios are monotone.
    thm:conclusion-collision-moment-stieltjes-hankel-positivity -/
theorem paper_conclusion_collision_moment_stieltjes_hankel_positivity (m : ℕ) :
    collisionMomentHankelPrincipalMinorsNonneg m ∧
      collisionMomentAdjacentMomentsLogConvex m ∧
      collisionMomentSuccessiveRatioMonotone m := by
  refine ⟨?_, ?_, ?_⟩
  · intro q
    have hq : Omega.momentSum (q + 1) m ^ 2 ≤ Omega.momentSum q m * Omega.momentSum (q + 2) m :=
      Omega.momentSum_log_convex q m
    have hqZ :
        ((Omega.momentSum (q + 1) m : ℤ) ^ 2 ≤
          (Omega.momentSum q m : ℤ) * Omega.momentSum (q + 2) m) := by
      exact_mod_cast hq
    unfold collisionMomentAdjacentHankelMinor
    linarith
  · intro q
    exact Omega.momentSum_log_convex q m
  · intro q
    have hq : Omega.momentSum (q + 1) m ^ 2 ≤ Omega.momentSum q m * Omega.momentSum (q + 2) m :=
      Omega.momentSum_log_convex q m
    have hq0 : (0 : ℚ) < Omega.momentSum q m := by
      exact_mod_cast Omega.momentSum_pos' q m
    have hq1 : (0 : ℚ) < Omega.momentSum (q + 1) m := by
      exact_mod_cast Omega.momentSum_pos' (q + 1) m
    have hq_cast :
        (Omega.momentSum (q + 1) m : ℚ) ^ 2 ≤
          (Omega.momentSum q m : ℚ) * Omega.momentSum (q + 2) m := by
      exact_mod_cast hq
    exact (div_le_div_iff₀ hq0 hq1).2 (by
      simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hq_cast)

end Omega.Conclusion
