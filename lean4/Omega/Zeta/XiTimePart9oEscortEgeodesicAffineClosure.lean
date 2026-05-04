import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part9o-escort-egeodesic-affine-closure`. -/
theorem paper_xi_time_part9o_escort_egeodesic_affine_closure (φ p q «λ» : ℝ) :
    (fun s : ℝ => -s * Real.log φ) («λ» * p + (1 - «λ») * q) =
      «λ» * (fun s : ℝ => -s * Real.log φ) p +
        (1 - «λ») * (fun s : ℝ => -s * Real.log φ) q := by
  ring

end Omega.Zeta
