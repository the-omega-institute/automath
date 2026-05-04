import Mathlib.Tactic

namespace Omega.Zeta

open scoped ComplexConjugate

/-- Paper label: `thm:xi-toeplitz-diskpole-scan-node-antiholomorphic-conjugacy`. -/
theorem paper_xi_toeplitz_diskpole_scan_node_antiholomorphic_conjugacy
    (Δ γ δ : ℝ) (a : ℂ)
    (hcayley :
      conj (((1 : ℂ) + a) / ((1 : ℂ) - a)) =
        (δ : ℂ) + Complex.I * (γ : ℂ)) :
    Complex.exp (-(((1 : ℂ) + (δ : ℂ)) * (Δ : ℂ))) *
      Complex.exp (-(Complex.I * (γ : ℂ) * (Δ : ℂ))) =
        Complex.exp (-(Δ : ℂ)) *
          Complex.exp (-((Δ : ℂ) *
            conj (((1 : ℂ) + a) / ((1 : ℂ) - a)))) := by
  rw [hcayley]
  rw [← Complex.exp_add, ← Complex.exp_add]
  ring_nf

end Omega.Zeta
