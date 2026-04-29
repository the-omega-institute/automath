import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-symq-golden-cq-pi-adic-kernel-growth`. -/
theorem paper_xi_symq_golden_cq_pi_adic_kernel_growth (q t : Nat) (Sigma ker : Nat → Nat)
    (hStep : Sigma (t + 1) = Sigma t + (q - t)) (hKer : ∀ u, ker u = 5 ^ Sigma u) :
    ker (t + 1) = 5 ^ (q - t) * ker t := by
  rw [hKer (t + 1), hKer t, hStep, pow_add]
  ring

end Omega.Zeta
