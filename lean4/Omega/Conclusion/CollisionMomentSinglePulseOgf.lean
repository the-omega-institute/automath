import Mathlib.Tactic
import Omega.Conclusion.CollisionMomentMinrecHaltingTime

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-collision-moment-single-pulse-ogf`. The halting profile from the
minimal-recurrence theorem is exactly a single step function, hence the sequence is constant `2`
in the non-halting case and differs from it by one pulse at the halting threshold in the halting
case. -/
theorem paper_conclusion_collision_moment_single_pulse_ogf (h : CollisionMomentMinrecHaltingTimeData) :
    (h.halts -> forall n, h.seq n = 2 + (2 ^ h.q - 2) * (if h.haltingSteps <= n then 1 else 0)) /\
      (Not h.halts -> forall n, h.seq n = 2) := by
  rcases paper_conclusion_collision_moment_minrec_halting_time h with ⟨hnonhalt, hhalt, _⟩
  refine ⟨?_, ?_⟩
  · intro hh n
    have hseq := hhalt hh n
    by_cases hle : h.haltingSteps ≤ n
    · have hpow_ge_two : 2 ≤ 2 ^ h.q := h.halting_power_ge_two hh
      have hvalue : h.seq n = 2 ^ h.q := by
        rw [hseq]
        exact by simp [Nat.not_lt.mpr hle]
      calc
        h.seq n = 2 ^ h.q := hvalue
        _ = 2 + (2 ^ h.q - 2) := by symm; exact Nat.add_sub_of_le hpow_ge_two
        _ = 2 + (2 ^ h.q - 2) * (if h.haltingSteps <= n then 1 else 0) := by simp [hle]
    · have hlt : n < h.haltingSteps := Nat.lt_of_not_ge hle
      rw [hseq]
      simp [hlt, hle]
  · intro hnh n
    simpa using congrFun (hnonhalt hnh) n

end Omega.Conclusion
