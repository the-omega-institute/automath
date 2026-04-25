import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.SyncKernelWeighted.RealInput40NilpotentIndex

namespace Omega.SyncKernelWeighted

open scoped BigOperators

/-- Split state into its persistent essential coordinate and its transient five-step nilpotent
complement. -/
abbrev real_input_40_nilpotent_memory_depth_state := ℝ × (Fin 5 → ℝ)

/-- After `m` steps only the transient coordinates with index at least `m` can survive. -/
def real_input_40_nilpotent_memory_depth_transient_after (m : ℕ) (w : Fin 5 → ℝ) :
    Fin 5 → ℝ := fun i =>
  if h : i.1 + m < 5 then
    w ⟨i.1 + m, h⟩
  else
    0

/-- The full seed dynamics keeps the essential component and evolves the transient block by the
five-step nilpotent shift. -/
def real_input_40_nilpotent_memory_depth_after (m : ℕ)
    (w : real_input_40_nilpotent_memory_depth_state) :
    real_input_40_nilpotent_memory_depth_state :=
  (w.1, real_input_40_nilpotent_memory_depth_transient_after m w.2)

/-- Bilinear observable testing whether the transient part is still visible after `m` steps. -/
def real_input_40_nilpotent_memory_depth_observable
    (v w : real_input_40_nilpotent_memory_depth_state) : ℝ :=
  v.1 * w.1 + ∑ i, v.2 i * w.2 i

lemma real_input_40_nilpotent_memory_depth_transient_after_eq_zero
    (m : ℕ) (hm : 5 ≤ m) (w : Fin 5 → ℝ) :
    real_input_40_nilpotent_memory_depth_transient_after m w = 0 := by
  funext i
  by_cases h : i.1 + m < 5
  · omega
  · simp [real_input_40_nilpotent_memory_depth_transient_after, h]

/-- Paper label: `cor:real-input-40-nilpotent-memory-depth`. The previously verified nilpotent
index bounds stabilize at `3` for the essential kernel and `5` for the full kernel. In the
concrete split model, every power `m ≥ 5` kills the transient five-step chain, so the bilinear
observable only sees the essential component and is independent of the transient input. -/
theorem paper_real_input_40_nilpotent_memory_depth (m : ℕ) (hm : 5 ≤ m)
    (v : real_input_40_nilpotent_memory_depth_state) (e : ℝ) (wT : Fin 5 → ℝ) :
    real_input_40_nilpotent_index_essential_kernel_dim 3 = 11 ∧
      real_input_40_nilpotent_index_full_kernel_dim m = 31 ∧
      real_input_40_nilpotent_memory_depth_observable v
          (real_input_40_nilpotent_memory_depth_after m (e, wT)) =
        real_input_40_nilpotent_memory_depth_observable v
          (real_input_40_nilpotent_memory_depth_after m (e, 0)) := by
  rcases paper_real_input_40_nilpotent_index with
    ⟨_, _, hessential, _, _, _, _, _, _, hfull⟩
  have htrans :
      real_input_40_nilpotent_memory_depth_transient_after m wT = 0 :=
    real_input_40_nilpotent_memory_depth_transient_after_eq_zero m hm wT
  have hzero :
      real_input_40_nilpotent_memory_depth_transient_after m 0 = 0 := by
    funext i
    simp [real_input_40_nilpotent_memory_depth_transient_after]
  refine ⟨hessential, hfull m hm, ?_⟩
  simp [real_input_40_nilpotent_memory_depth_observable,
    real_input_40_nilpotent_memory_depth_after, htrans, hzero]

end Omega.SyncKernelWeighted
