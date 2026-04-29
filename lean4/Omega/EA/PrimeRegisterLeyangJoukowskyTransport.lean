import Omega.GU.JGLeyangDoubleResultant

namespace Omega.EA

/-- Paper label: `thm:prime-register-leyang-joukowsky-transport`. -/
theorem paper_prime_register_leyang_joukowsky_transport {K : Type*} [Field K]
    (r z z₁ z₂ : K) (hr : r ≠ 0) (hz : z ≠ 0) :
    Omega.GU.jgLeyangDoubleResultant r z z₁ z₂ = 0 ↔
      Omega.GU.LeyangHolographicN2.P z z₁ z₂ = 0 ∨
        Omega.GU.quadraticReciprocalEval (r ^ 2 * z) z₁ z₂ = 0 := by
  simpa using (Omega.GU.paper_group_jg_leyang_double_resultant r z z₁ z₂ hr hz).2

end Omega.EA
