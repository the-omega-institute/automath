import Mathlib.Tactic
import Omega.CircleDimension.CircleDim
import Omega.POM.MultiAxisNear1PoleBarrier

namespace Omega.CircleDimension

/-- Paper label: `thm:xi-cdim-driven-near1-pole-approach-law`.

Once the budget is normalized to the circle-dimension growth scale `B_n = (n + 1)^r`, the
multi-axis near-`1` pole barrier gives the explicit `B_n^{-2/d}` pole-gap bound. In this concrete
wrapper the free-rank input is recorded by `circleDim r t = r`. -/
theorem paper_xi_cdim_driven_near1_pole_approach_law
    {d : ℕ} (r t : ℕ) (sigmaDiag : Fin d → ℝ) (Λ : Finset (Fin d → ℝ)) (hΛ : Λ.Nonempty)
    (Vd detSigma logLambda : ℝ) (n : ℕ) (radius deltaSpec poleGap : ℝ) (θ : Fin d → ℝ)
    (hθΛ : θ ∈ Λ)
    (hθ : Omega.POM.pomQuadraticEnergy sigmaDiag θ ≤ radius ^ 2)
    (hr : radius ^ 2 =
      Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma ((n + 1 : ℝ) ^ r))
    (hgap : deltaSpec = (1 / 2 : ℝ) * Omega.POM.pomShortestEnergy sigmaDiag Λ hΛ)
    (hpole : poleGap = deltaSpec / logLambda) (hlog : 0 < logLambda) :
    circleDim r t = r ∧
      poleGap ≤
        Omega.POM.pomMinkowskiBudgetUpperBound d Vd detSigma ((n + 1 : ℝ) ^ r) /
          (2 * logLambda) := by
  refine ⟨by simp [circleDim], ?_⟩
  simpa using
    (Omega.POM.paper_pom_multi_axis_near1_pole_barrier sigmaDiag Λ hΛ Vd detSigma
      (((n + 1 : ℝ) ^ r)) radius deltaSpec poleGap logLambda θ hθΛ hθ hr hgap hpole hlog)

end Omega.CircleDimension
