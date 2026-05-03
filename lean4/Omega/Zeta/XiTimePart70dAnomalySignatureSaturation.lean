import Mathlib.Tactic
import Omega.Zeta.XiTimePart65BinfoldGaugeCenterAbelianizationExact

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70d-anomaly-signature-saturation`. -/
theorem paper_xi_time_part70d_anomaly_signature_saturation {m : ℕ}
    (fiber : Fin (Nat.fib (m + 2)) → ℕ) (hge : ∀ w, 2 ≤ fiber w) :
    Omega.OperatorAlgebra.foldGaugeAbelianizationOrder fiber = 2 ^ Nat.fib (m + 2) := by
  classical
  have hexact :=
    (paper_xi_time_part65_binfold_gauge_center_abelianization_exact fiber).2
  have hcard :
      (Finset.univ.filter fun w : Fin (Nat.fib (m + 2)) => 2 ≤ fiber w).card =
        Nat.fib (m + 2) := by
    simp [hge]
  simpa [hcard] using hexact

end Omega.Zeta
