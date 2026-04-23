import Omega.SyncKernelWeighted.RealInput40PrimitiveLucas
import Omega.SyncKernelWeighted.RealInput40TraceRecurrence

namespace Omega.SyncKernelWeighted

/-- Paper label: `cor:real-input-40-trace-tensor`. The audited real-input-40 trace sequence was
already normalized to the Lucas-square closed form, so the appendix tensor corollary is exactly
that closed form restated at the sequence level. -/
theorem paper_real_input_40_trace_tensor :
    ∀ n : ℕ,
      realInput40TraceSequence n =
        (Omega.lucasNum n : ℤ) ^ 2 + (-1 : ℤ) ^ n * ((Omega.lucasNum n : ℤ) + 1) + 2 := by
  intro n
  simp [realInput40TraceSequence]

end Omega.SyncKernelWeighted
