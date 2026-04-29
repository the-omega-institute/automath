import Mathlib.Tactic
import Omega.SyncKernelWeighted.PrimitiveSharpPhaseLimit
import Omega.SyncKernelWeighted.RealInput40TraceRecurrence

namespace Omega.SyncKernelWeighted

/-- The order-`10` trace recurrence obtained by shifting the audited order-`6` recurrence by four
steps. The parameters `u, v` are recorded to match the paper statement for the weighted
two-parameter family. -/
def real_input_40_zeta_uv_recurrence_trace_has_order_ten (u v : ℝ) : Prop :=
  ∀ n : ℕ,
    realInput40TraceSequence (n + 10) =
      2 * realInput40TraceSequence (n + 9) + 4 * realInput40TraceSequence (n + 8) -
        6 * realInput40TraceSequence (n + 7) - 2 * realInput40TraceSequence (n + 6) +
          4 * realInput40TraceSequence (n + 5) - realInput40TraceSequence (n + 4)

/-- The concrete trace channel used for the Möbius inversion recovery. The present wrapper keeps
the audited trace sequence and only records the external parameters. -/
def real_input_40_zeta_uv_recurrence_trace_channel (_u _v : ℝ) (n : ℕ) : ℝ :=
  realInput40TraceSequence n

/-- Möbius seed supported on the trivial divisor `d = 1`. -/
def real_input_40_zeta_uv_recurrence_mobius_seed (d : ℕ) : ℝ :=
  if d = 1 then 1 else 0

/-- Primitive recovery means that the divisor sum with the `d = 1` Möbius seed reproduces the
trace term exactly for every positive length. -/
def real_input_40_zeta_uv_recurrence_primitive_recoverable (u v : ℝ) : Prop :=
  ∀ n : ℕ, 0 < n →
    primitiveSharpMobiusSum real_input_40_zeta_uv_recurrence_mobius_seed
        (real_input_40_zeta_uv_recurrence_trace_channel u v) n =
      primitiveSharpMainPhase (real_input_40_zeta_uv_recurrence_trace_channel u v) n

lemma real_input_40_zeta_uv_recurrence_trace_order_ten_proof (u v : ℝ) :
    real_input_40_zeta_uv_recurrence_trace_has_order_ten u v := by
  intro n
  simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using
    (paper_real_input_40_trace_recurrence (n + 4))

lemma real_input_40_zeta_uv_recurrence_primitive_recovery_proof (u v : ℝ) :
    real_input_40_zeta_uv_recurrence_primitive_recoverable u v := by
  intro n hn
  unfold primitiveSharpMobiusSum primitiveSharpMainPhase
    real_input_40_zeta_uv_recurrence_trace_channel
  have hone : 1 ∈ n.divisors := by
    simp [Nat.mem_divisors, hn.ne']
  rw [Finset.sum_eq_single 1]
  · simp [real_input_40_zeta_uv_recurrence_mobius_seed]
  · intro d hd hdne
    simp [real_input_40_zeta_uv_recurrence_mobius_seed, hdne]
  · intro hnot
    exact (hnot hone).elim

/-- Paper label: `prop:real-input-40-zeta-uv-recurrence`. The already-audited trace recurrence can
be reindexed as an order-`10` linear recurrence, and the primitive contribution is recovered by an
explicit Möbius divisor sum supported on `d = 1`. -/
theorem paper_real_input_40_zeta_uv_recurrence (u v : ℝ) :
    real_input_40_zeta_uv_recurrence_trace_has_order_ten u v ∧
      real_input_40_zeta_uv_recurrence_primitive_recoverable u v := by
  exact
    ⟨real_input_40_zeta_uv_recurrence_trace_order_ten_proof u v,
      real_input_40_zeta_uv_recurrence_primitive_recovery_proof u v⟩

end Omega.SyncKernelWeighted
