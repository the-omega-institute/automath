import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:xi-time-part9gb-prime-register-dimension-complement`. -/
theorem paper_xi_time_part9gb_prime_register_dimension_complement
    (L fullDim zgDim fullRate zgRate : Real)
    (hfull : L * fullDim = fullRate) (hzg : L * zgDim = zgRate) :
    L * (1 - fullDim) = L - fullRate ∧ L * (1 - zgDim) = L - zgRate := by
  constructor
  · rw [← hfull]
    ring
  · rw [← hzg]
    ring

end Omega.Zeta
