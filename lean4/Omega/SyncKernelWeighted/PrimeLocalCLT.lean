import Omega.SyncKernelWeighted.EdgeworthFourth
import Omega.SyncKernelWeighted.PrimitiveSharpPhaseLimit

namespace Omega.SyncKernelWeighted

/-- Paper label: `thm:prime-local-clt`.
The local Gaussian variance is the audited value `11 / 102`, and the primitive Möbius/Witt
decomposition leaves a `d = 1` main phase plus an exponentially small divisor tail on the local
window. -/
theorem paper_prime_local_clt
    (μ : ℕ → ℝ) (centeredTrace : ℕ → ℝ) (Λ : ℝ) (n : ℕ)
    (hn : 0 < n) (hΛ : 0 ≤ Λ) (hμ1 : μ 1 = 1)
    (hμtail : ∀ d ∈ n.divisors.erase 1, |μ d| ≤ 1)
    (htraceTail : ∀ d ∈ n.divisors.erase 1, |centeredTrace (n / d)| ≤ Λ ^ n) :
    edgeworthSigmaSq = 11 / 102 ∧
      PrimitiveSharpPhaseLimitStatement μ centeredTrace Λ n := by
  refine ⟨paper_edgeworth_fourth.1, ?_⟩
  exact paper_primitive_sharp_phase_limit μ centeredTrace Λ n hn hΛ hμ1 hμtail htraceTail

end Omega.SyncKernelWeighted
