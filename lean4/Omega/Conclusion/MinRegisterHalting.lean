import Mathlib.Tactic
import Omega.Conclusion.MinimalStateComplexityHalting

namespace Omega.Conclusion

/-- The reachable-state budget of a synchronous NAND circuit with `k` binary registers. -/
def nandRegisterStateBudget (k : ℕ) : ℕ :=
  2 ^ k

/-- The minimal register count forced by a state-space lower bound `s ≤ 2^k`. -/
def minRegisterCountFromStateCount (s : ℕ) : ℕ :=
  Nat.clog 2 s

/-- Paper-facing halting corollary for the NAND-plus-register model: once the nonhalting branch
collapses to one reachable state while one-step padding forces at least two states in the halting
branch, the minimal binary register count detects halting.
    cor:conclusion-min-register-halting -/
def conclusionMinRegisterHalting : Prop :=
  ∀ h padded : ConclusionMinimalStateComplexityHaltingData,
    h.uniformBound = 1 →
    1 ≤ h.minStateCount →
    (h.halts ↔ padded.halts) →
    (h.halts → 1 ≤ padded.haltingSteps) →
    (¬ h.halts → minRegisterCountFromStateCount h.minStateCount = 0) ∧
      (padded.halts → 1 ≤ minRegisterCountFromStateCount padded.minStateCount)

/-- Paper label: `cor:conclusion-min-register-halting`. -/
theorem paper_conclusion_min_register_halting : conclusionMinRegisterHalting := by
  intro h padded hunif hstatepos hsame hpadstep
  refine ⟨?_, ?_⟩
  · intro hnonhalting
    have hpkg := paper_conclusion_minimal_state_complexity_halting h
    have hle : h.minStateCount ≤ 1 := by
      rw [hunif] at hpkg
      exact hpkg.2.1 hnonhalting
    have heq : h.minStateCount = 1 := le_antisymm hle hstatepos
    simp [minRegisterCountFromStateCount, heq]
  · intro hhalting
    have hpad := paper_conclusion_minimal_state_complexity_halting padded
    have hEq : padded.minStateCount = padded.haltingSteps + 1 := hpad.1 hhalting
    have horig : h.halts := hsame.mpr hhalting
    have hstep : 1 ≤ padded.haltingSteps := hpadstep horig
    have htwo : 2 ≤ padded.minStateCount := by
      rw [hEq]
      exact Nat.succ_le_succ hstep
    have hone : 1 < padded.minStateCount := lt_of_lt_of_le (by norm_num) htwo
    have hclog_pos : 0 < minRegisterCountFromStateCount padded.minStateCount := by
      unfold minRegisterCountFromStateCount
      exact Nat.clog_pos (by norm_num) hone
    exact Nat.succ_le_of_lt hclog_pos

end Omega.Conclusion
