import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

namespace Omega.POM

/-- Concrete channel package for the Schur near-RH margin propagation statement. The channel
exponent is the logarithmic radius supplied by the Schur packet, while `primeShadow` is the
nontrivial prime-shadow contribution controlled by the same radius. -/
structure pom_schur_near_rh_margin_propagation_Context where
  channelCount : ℕ
  pressure : ℝ
  delta : ℝ
  channelExponent : Fin channelCount → ℝ
  spectralRadius : Fin channelCount → ℝ
  primeShadow : Fin channelCount → ℕ → ℝ
  primeShadowConstant : Fin channelCount → ℝ
  spectralRadius_eq_exp : ∀ lam, spectralRadius lam = Real.exp (channelExponent lam)
  primeShadow_template :
    ∀ lam N, 2 ≤ N →
      primeShadow lam N ≤
        primeShadowConstant lam * Real.exp (((pressure - delta) / 2) * (N : ℝ)) / (N : ℝ)

/-- Uniform linear Schur margin against every nontrivial channel exponent. -/
def pom_schur_near_rh_margin_propagation_Context.margin_hypothesis
    (D : pom_schur_near_rh_margin_propagation_Context) : Prop :=
  0 < D.delta ∧ ∀ lam, 2 * D.channelExponent lam ≤ D.pressure - D.delta

/-- Spectral-radius version of the uniform Schur margin. -/
def pom_schur_near_rh_margin_propagation_Context.spectral_gap_bound
    (D : pom_schur_near_rh_margin_propagation_Context) : Prop :=
  ∀ lam, D.spectralRadius lam ≤ Real.exp ((D.pressure - D.delta) / 2)

/-- Prime-shadow deviation estimate with exponent inherited from the Schur spectral margin. -/
def pom_schur_near_rh_margin_propagation_Context.prime_deviation_bound
    (D : pom_schur_near_rh_margin_propagation_Context) : Prop :=
  ∀ lam N, 2 ≤ N →
    D.primeShadow lam N ≤
      D.primeShadowConstant lam *
          Real.exp (((D.pressure - D.delta) / 2) * (N : ℝ)) / (N : ℝ)

/-- Paper label: `cor:pom-schur-near-rh-margin-propagation`. -/
theorem paper_pom_schur_near_rh_margin_propagation
    (D : pom_schur_near_rh_margin_propagation_Context) :
    D.margin_hypothesis -> D.spectral_gap_bound ∧ D.prime_deviation_bound := by
  intro hmargin
  refine ⟨?_, ?_⟩
  · intro lam
    rw [D.spectralRadius_eq_exp lam]
    exact Real.exp_le_exp.mpr (by linarith [hmargin.2 lam])
  · intro lam N hN
    exact D.primeShadow_template lam N hN

end Omega.POM
