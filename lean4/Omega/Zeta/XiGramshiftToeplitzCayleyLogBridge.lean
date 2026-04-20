import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import Mathlib.Analysis.SpecialFunctions.Complex.Log

namespace Omega.Zeta

open Complex

/-- The exponential Gram-shift node parametrization `z = exp(-(1+δ)) exp(-iγ)`. -/
noncomputable def xiGramshiftNode (δ γ : ℝ) : ℂ :=
  Complex.exp (-(1 + δ)) * Complex.exp (-γ * Complex.I)

/-- The Cayley compactification evaluated at `γ + iδ`. -/
noncomputable def xiCayley (γ δ : ℝ) : ℂ :=
  (((γ : ℂ) + δ * Complex.I) - Complex.I) / (((γ : ℂ) + δ * Complex.I) + Complex.I)

/-- The disk-coordinate bridge `Φ(z) = C(-Arg z + i(-log |z| - 1))`. -/
noncomputable def xiPhi (z : ℂ) : ℂ :=
  xiCayley (-Complex.arg z) (-Real.log ‖z‖ - 1)

/-- Paper-facing Cayley/log bridge for the Gram-shift node parametrization: once the argument
and radius are read off from `z`, direct substitution gives the Toeplitz pole.
    thm:xi-gramshift-toeplitz-cayley-log-bridge -/
theorem paper_xi_gramshift_toeplitz_cayley_log_bridge (δ γ : ℝ)
    (hArg : Complex.arg (xiGramshiftNode δ γ) = -γ)
    (hAbs : ‖xiGramshiftNode δ γ‖ = Real.exp (-(1 + δ))) :
    xiCayley γ δ = xiPhi (xiGramshiftNode δ γ) := by
  have hδ : -Real.log (Real.exp (-(1 + δ))) - 1 = δ := by
    rw [Real.log_exp]
    ring
  unfold xiPhi
  rw [hArg, hAbs, hδ, neg_neg]

end Omega.Zeta
