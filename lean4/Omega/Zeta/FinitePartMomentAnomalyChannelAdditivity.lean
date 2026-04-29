import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:finite-part-moment-anomaly-channel-additivity`. Once the constant layer is
split into its trivial-channel part and the finite sum of nontrivial channel contributions, the
moment anomaly is additive by ordinary finite-sum algebra. -/
theorem paper_finite_part_moment_anomaly_channel_additivity {ι : Type*} [Fintype ι]
    (q : ℕ) (Cq C1 Ctriv : ℝ) (f Phi : ι → ℝ)
    (hCq : Cq = Ctriv + ∑ lam, f lam * Phi lam) :
    Cq - (q : ℝ) * C1 = (Ctriv - (q : ℝ) * C1) + ∑ lam, f lam * Phi lam := by
  subst Cq
  ring

end Omega.Zeta
