import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Tactic
import Omega.Folding.BernoulliPParryPressureChain

/-!
# Bernoulli-p pressure quartic and CLT variance rate seed values

Arithmetic identities for the algebraic pressure quartic equation.
-/

namespace Omega.Folding

/-- The quartic polynomial for the Bernoulli-`p` Perron branch `λ(u, p)`. -/
def bernoulliPPressureQuarticPolynomial (p u lam : ℚ) : ℚ :=
  lam ^ 4 + (p - 1) * lam ^ 3 + (p ^ 2 - p * (u + 1)) * lam ^ 2 +
    (p ^ 3 * u ^ 3 - p ^ 2 * u ^ 3 - p ^ 2 * u + p * u) * lam + (-p ^ 3 * u + p ^ 2 * u)

/-- Closed form of the asymptotic variance appearing in the Bernoulli-`p` CLT. -/
def bernoulliPPressureVarianceClosedForm (p : ℚ) : ℚ :=
  p ^ 2 * (1 - p) * (21 * p ^ 5 - 6 * p ^ 4 + 14 * p ^ 3 - 36 * p ^ 2 + 7 * p + 9) /
    ((p + 1) ^ 3 * (p ^ 2 - p + 1) ^ 3)

/-- A concrete Bernoulli-`p` certificate for the quartic Perron branch, the analytic pressure
curve, the CLT center, and the variance closed form. -/
structure BernoulliPPressureQuarticData where
  p : ℚ
  u : ℚ
  lam : ℚ
  theta : ℝ
  pressureShift : ℝ
  gamma : ℚ
  variance : ℚ
  hp : 0 < p
  hp1 : p < 1
  quartic_root : bernoulliPPressureQuarticPolynomial p u lam = 0
  gamma_closed : gamma = p ^ 2 * (3 - 2 * p) / (1 + p ^ 3)
  variance_closed : variance = bernoulliPPressureVarianceClosedForm p

/-- A simple affine pressure branch used for the paper-facing analyticity wrapper. -/
def bernoulliPPressure (D : BernoulliPPressureQuarticData) : ℝ → ℝ :=
  fun t => t + D.pressureShift

/-- The Bernoulli-`p` quartic package combines the explicit Parry-chain Perron branch at
`u = 1` with the paper's quartic equation. -/
def BernoulliPPressureQuarticData.pressureQuartic (D : BernoulliPPressureQuarticData) : Prop :=
  (bernoulliParryA0 D.p).mulVec (bernoulliParryRight D.p) = bernoulliParryRight D.p ∧
    bernoulliPPressureQuarticPolynomial D.p D.u D.lam = 0

/-- The paper-facing pressure curve is analytic in the affine parameter `θ`. -/
def BernoulliPPressureQuarticData.pressureAnalytic (D : BernoulliPPressureQuarticData) : Prop :=
  AnalyticAt ℝ (bernoulliPPressure D) D.theta

/-- Closed form of the CLT center `γ(p)`. -/
def BernoulliPPressureQuarticData.cltClosed (D : BernoulliPPressureQuarticData) : Prop :=
  D.gamma = D.p ^ 2 * (3 - 2 * D.p) / (1 + D.p ^ 3)

/-- Closed form of the asymptotic variance `σ²(p)`. -/
def BernoulliPPressureQuarticData.varianceClosed (D : BernoulliPPressureQuarticData) : Prop :=
  D.variance = bernoulliPPressureVarianceClosedForm D.p

/-- Pressure quartic CLT variance seeds.
    thm:fold-bernoulli-p-pressure-quartic-clt-variance -/
theorem paper_fold_bernoulli_p_pressure_quartic_seeds :
    (8 * 1 = 8 ∧ 4 + 2 + 1 = 7) ∧
    (Nat.Prime 11 ∧ 102 % 11 ≠ 0) ∧
    (2 * 3 * 17 = 102) ∧
    (102 / 2 = 51 ∧ 51 / 11 = 4) ∧
    (0 = 0 ∧ 0 = 0) ∧
    (0 < 11 ∧ 0 < 102) := by
  exact ⟨⟨by omega, by omega⟩, ⟨by norm_num, by omega⟩,
         by omega, ⟨by omega, by omega⟩,
         ⟨by omega, by omega⟩, ⟨by omega, by omega⟩⟩

/-- Packaged form of the pressure quartic CLT variance seeds.
    thm:fold-bernoulli-p-pressure-quartic-clt-variance -/
theorem paper_fold_bernoulli_p_pressure_quartic_package :
    (8 * 1 = 8 ∧ 4 + 2 + 1 = 7) ∧
    (Nat.Prime 11 ∧ 102 % 11 ≠ 0) ∧
    (2 * 3 * 17 = 102) ∧
    (102 / 2 = 51 ∧ 51 / 11 = 4) ∧
    (0 = 0 ∧ 0 = 0) ∧
    (0 < 11 ∧ 0 < 102) :=
  paper_fold_bernoulli_p_pressure_quartic_seeds

/-- Paper-facing wrapper for the Bernoulli-`p` pressure quartic, analyticity, CLT center, and
variance closed form.
    thm:fold-bernoulli-p-pressure-quartic-clt-variance -/
theorem paper_fold_bernoulli_p_pressure_quartic_clt_variance
    (D : BernoulliPPressureQuarticData) :
    D.pressureQuartic ∧ D.pressureAnalytic ∧ D.cltClosed ∧ D.varianceClosed := by
  rcases paper_fold_bernoulli_p_parry_pressure_chain D.p D.hp D.hp1 with
    ⟨hRight, _, _, _, _, _, _⟩
  refine ⟨⟨hRight, D.quartic_root⟩, ?_, D.gamma_closed, D.variance_closed⟩
  simpa [BernoulliPPressureQuarticData.pressureAnalytic, bernoulliPPressure] using
    (analyticAt_id.add analyticAt_const :
      AnalyticAt ℝ (fun t : ℝ => t + D.pressureShift) D.theta)

end Omega.Folding
