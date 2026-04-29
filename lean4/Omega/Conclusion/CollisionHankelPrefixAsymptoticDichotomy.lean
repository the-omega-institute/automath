import Mathlib.Tactic
import Omega.Conclusion.CollisionMomentMinrecHaltingTime

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-collision-hankel-prefix-asymptotic-dichotomy`. The explicit
collision-moment halting profile collapses every sufficiently far Hankel tail to the plateau
value, while the non-halting profile is constantly `2`. -/
theorem paper_conclusion_collision_hankel_prefix_asymptotic_dichotomy
    (h : CollisionMomentMinrecHaltingTimeData) :
    (h.halts → h.minRecurrenceOrder = h.haltingSteps + 1 ∧
        (∀ N i j, h.haltingSteps ≤ N → h.seq (N + i + j) = 2 ^ h.q)) ∧
      (¬ h.halts → h.minRecurrenceOrder = 1 ∧ ∀ N i j, h.seq (N + i + j) = 2) := by
  rcases paper_conclusion_collision_moment_minrec_halting_time h with ⟨hnonhalt, hhalt, hmin⟩
  refine ⟨?_, ?_⟩
  · intro hh
    refine ⟨?_, ?_⟩
    · simpa [hh] using hmin
    · intro N i j hN
      have htail : ¬ N + i + j < h.haltingSteps := by omega
      rw [hhalt hh (N + i + j)]
      simp [htail]
  · intro hnh
    refine ⟨?_, ?_⟩
    · simpa [hnh] using hmin
    · intro N i j
      simpa using congrFun (hnonhalt hnh) (N + i + j)

end Omega.Conclusion
