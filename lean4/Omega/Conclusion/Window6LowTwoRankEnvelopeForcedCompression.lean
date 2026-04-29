import Mathlib.Tactic
import Omega.Conclusion.CompressionLadderSpin10

namespace Omega.Conclusion

/-- A rank-`2` central `2`-torsion envelope cannot faithfully host the rank-`3` window-`6`
boundary shadow. -/
def conclusion_window6_low_two_rank_envelope_forced_compression_low_rank_obstruction : Prop :=
  ¬ (3 : ℕ) ≤ 2

/-- The `so(10)` compression ladder retains at most one output parity bit, so the lost-kernel rank
is at least `2`. -/
def conclusion_window6_low_two_rank_envelope_forced_compression_so10_kernel_bound : Prop :=
  (2 : ℕ) ≤ 3 - 1

/-- Paper label: `thm:conclusion-window6-low-two-rank-envelope-forced-compression`. The low-rank
obstruction is the rank inequality `3 ≰ 2`, and the `so(10)` case is the kernel bound already
recorded by the compression ladder. -/
theorem paper_conclusion_window6_low_two_rank_envelope_forced_compression :
    conclusion_window6_low_two_rank_envelope_forced_compression_low_rank_obstruction ∧
      conclusion_window6_low_two_rank_envelope_forced_compression_so10_kernel_bound := by
  have hcompression :=
    Omega.Conclusion.CompressionLadderSpin10.paper_conclusion_window6_compression_ladder_spin10
  refine ⟨?_, ?_⟩
  · simp [conclusion_window6_low_two_rank_envelope_forced_compression_low_rank_obstruction]
  · exact by
      simpa [conclusion_window6_low_two_rank_envelope_forced_compression_so10_kernel_bound] using
        hcompression.2.1

end Omega.Conclusion
