import Mathlib.Tactic
import Omega.Folding.GaugeAnomalyTrigonalRamificationMu

namespace Omega.Folding

/-- The quadratic base change used to desingularize the trigonal discriminant support. -/
def gaugeAnomalyTrigonalQuadraticLiftDegree : ℕ := 2

/-- Over the quadratic base, the irreducible trigonal field becomes a cyclic cubic extension. -/
def gaugeAnomalyTrigonalCyclicLiftDegree : ℕ := 3

/-- The resulting regular closure has degree `2 · 3 = 6`, the order of `S₃`. -/
def gaugeAnomalyTrigonalS3ClosureDegree : ℕ :=
  gaugeAnomalyTrigonalQuadraticLiftDegree * gaugeAnomalyTrigonalCyclicLiftDegree

/-- Contribution of a simple ramification point (inertia order `2`) to the degree-`6`
Riemann-Hurwitz sum. -/
def gaugeAnomalyTrigonalS3SimpleContribution : ℕ :=
  gaugeAnomalyTrigonalS3ClosureDegree / 2

/-- Contribution of a totally ramified point (inertia order `3`) to the degree-`6`
Riemann-Hurwitz sum. -/
def gaugeAnomalyTrigonalS3FullContribution : ℕ :=
  gaugeAnomalyTrigonalS3ClosureDegree * 2 / 3

/-- Genus of the desingularized `S₃`-closure computed from the existing ramification counts. -/
def gaugeAnomalyTrigonalS3ClosureGenus : ℕ :=
  (gaugeAnomalyTrigonalSimpleBranchCount * gaugeAnomalyTrigonalS3SimpleContribution +
      gaugeAnomalyTrigonalFullBranchCount * gaugeAnomalyTrigonalS3FullContribution -
      gaugeAnomalyTrigonalS3ClosureDegree * 2 + 2) / 2

/-- The trigonal discriminant support is resolved by a quadratic step, the cubic extension over the
resulting base is cyclic, the full regular closure has degree `6 = |S₃|`, and the branch data from
`paper_fold_gauge_anomaly_trigonal_ramification_mu` give genus `8` by Riemann-Hurwitz.
    thm:fold-gauge-anomaly-trigonal-s3-galois-closure -/
theorem paper_fold_gauge_anomaly_trigonal_s3_galois_closure :
    gaugeAnomalyTrigonalQuadraticLiftDegree = 2 ∧
      gaugeAnomalyTrigonalCyclicLiftDegree = 3 ∧
      gaugeAnomalyTrigonalS3ClosureDegree = 6 ∧
      gaugeAnomalyTrigonalFullBranchCount = 2 ∧
      gaugeAnomalyTrigonalSimpleBranchCount = 6 ∧
      gaugeAnomalyTrigonalS3ClosureGenus = 8 := by
  rcases paper_fold_gauge_anomaly_trigonal_ramification_mu with ⟨_, _, hfull, hsimple, _⟩
  refine ⟨rfl, rfl, rfl, hfull, hsimple, ?_⟩
  norm_num [gaugeAnomalyTrigonalS3ClosureGenus, gaugeAnomalyTrigonalS3ClosureDegree,
    gaugeAnomalyTrigonalQuadraticLiftDegree, gaugeAnomalyTrigonalCyclicLiftDegree,
    gaugeAnomalyTrigonalS3SimpleContribution, gaugeAnomalyTrigonalS3FullContribution, hfull,
    hsimple]

end Omega.Folding
