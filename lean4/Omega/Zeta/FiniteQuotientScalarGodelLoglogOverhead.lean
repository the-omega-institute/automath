import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.ZMod.Basic

namespace Omega.Zeta

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: any code space for finite quotient data must be at least as large as the
    free quotient itself.
    thm:xi-finite-quotient-scalar-godel-loglog-overhead -/
theorem paper_xi_finite_quotient_scalar_godel_loglog_overhead_seeds
    (r n A T : ℕ) [NeZero n]
    (f : (Fin r → ZMod n) → Fin (A ^ T)) (hf : Function.Injective f) :
    n ^ r ≤ A ^ T := by
  simpa [Fintype.card_fun, Fintype.card_fin, ZMod.card] using Fintype.card_le_of_injective f hf

end Omega.Zeta
