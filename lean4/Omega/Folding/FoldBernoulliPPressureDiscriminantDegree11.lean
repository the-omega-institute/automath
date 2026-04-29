import Omega.Folding.BernoulliPPressureQuartic
import Omega.Folding.GaugeAnomalyLeyangBranchU1

namespace Omega.Folding

/-- The classical discriminant formula for a monic quartic
`x^4 + a x^3 + b x^2 + c x + d`. -/
def quarticDiscriminant (a b c d : ℚ) : ℚ :=
  256 * d ^ 3 - 192 * a * c * d ^ 2 - 128 * b ^ 2 * d ^ 2 + 144 * b * c ^ 2 * d -
    27 * c ^ 4 + 144 * a ^ 2 * b * d ^ 2 - 6 * a ^ 2 * c ^ 2 * d - 80 * a * b ^ 2 * c * d +
    18 * a * b * c ^ 3 + 16 * b ^ 4 * d - 4 * b ^ 3 * c ^ 2 - 27 * a ^ 4 * d ^ 2 +
    18 * a ^ 3 * b * c * d - 4 * a ^ 3 * c ^ 3 - 4 * a ^ 2 * b ^ 3 * d + a ^ 2 * b ^ 2 * c ^ 2

/-- The explicit `λ`-discriminant of the Bernoulli-`p` pressure quartic. -/
def bernoulliPPressureQuarticDiscriminant (u p : ℚ) : ℚ :=
  quarticDiscriminant (p - 1) (p ^ 2 - p * (u + 1))
    (p ^ 3 * u ^ 3 - p ^ 2 * u ^ 3 - p ^ 2 * u + p * u) (p ^ 2 * u * (1 - p))

/-- The degree-`11` residual factor `D(u,p)` from the paper statement. -/
def bernoulliPPressureResidualDiscriminant (u p : ℚ) : ℚ :=
  27 * p ^ 8 * u ^ 11 - 14 * p ^ 8 * u ^ 8 + 3 * p ^ 8 * u ^ 5 - 81 * p ^ 7 * u ^ 11 -
    90 * p ^ 7 * u ^ 9 + 52 * p ^ 7 * u ^ 8 + 170 * p ^ 7 * u ^ 6 - 11 * p ^ 7 * u ^ 5 -
    68 * p ^ 7 * u ^ 3 + 12 * p ^ 7 + 81 * p ^ 6 * u ^ 11 + 270 * p ^ 6 * u ^ 9 -
    68 * p ^ 6 * u ^ 8 - 25 * p ^ 6 * u ^ 7 - 536 * p ^ 6 * u ^ 6 + 14 * p ^ 6 * u ^ 5 +
    36 * p ^ 6 * u ^ 4 + 252 * p ^ 6 * u ^ 3 + 24 * p ^ 6 * u - 44 * p ^ 6 -
    27 * p ^ 5 * u ^ 11 - 270 * p ^ 5 * u ^ 9 + 28 * p ^ 5 * u ^ 8 - 57 * p ^ 5 * u ^ 7 +
    576 * p ^ 5 * u ^ 6 + 126 * p ^ 5 * u ^ 5 - 68 * p ^ 5 * u ^ 4 - 328 * p ^ 5 * u ^ 3 +
    36 * p ^ 5 * u ^ 2 - 40 * p ^ 5 * u + 56 * p ^ 5 + 90 * p ^ 4 * u ^ 9 +
    6 * p ^ 4 * u ^ 8 + 189 * p ^ 4 * u ^ 7 - 204 * p ^ 4 * u ^ 6 - 213 * p ^ 4 * u ^ 5 +
    176 * p ^ 4 * u ^ 3 - 36 * p ^ 4 * u ^ 2 - 16 * p ^ 4 * u - 24 * p ^ 4 -
    4 * p ^ 3 * u ^ 8 - 107 * p ^ 3 * u ^ 7 - 18 * p ^ 3 * u ^ 6 + 29 * p ^ 3 * u ^ 5 +
    60 * p ^ 3 * u ^ 4 + 20 * p ^ 3 * u ^ 3 - 16 * p ^ 3 * u ^ 2 + 48 * p ^ 3 * u -
    4 * p ^ 3 + 12 * p ^ 2 * u ^ 6 + 52 * p ^ 2 * u ^ 5 - 44 * p ^ 2 * u ^ 3 -
    8 * p ^ 2 * u + 4 * p ^ 2 - 12 * p * u ^ 4 - 8 * p * u ^ 3 + 12 * p * u ^ 2 -
    8 * p * u + 4 * u ^ 2

/-- Concrete degree-`11` discriminant statement for the Bernoulli-`p` pressure quartic. -/
def foldBernoulliPPressureDiscriminantDegree11Statement : Prop :=
  (∀ u p : ℚ,
    bernoulliPPressureQuarticDiscriminant u p =
      p ^ 3 * u * (1 - p) * bernoulliPPressureResidualDiscriminant u p) ∧
  (∀ p : ℚ,
    bernoulliPPressureResidualDiscriminant 1 p =
      4 * (1 + p) ^ 2 * (2 * p - 1) ^ 2 * (p ^ 2 - p + 1) ^ 2) ∧
  (∀ p : ℚ, 0 < p → p < 1 →
    (bernoulliPPressureResidualDiscriminant 1 p = 0 ↔ p = 1 / 2))

lemma bernoulliPPressureResidualDiscriminant_u1_eq_zero_iff (p : ℚ) (hp0 : 0 < p) (hp1 : p < 1) :
    bernoulliPPressureResidualDiscriminant 1 p = 0 ↔ p = 1 / 2 := by
  rw [show bernoulliPPressureResidualDiscriminant 1 p =
      4 * (1 + p) ^ 2 * (2 * p - 1) ^ 2 * (p ^ 2 - p + 1) ^ 2 by
    dsimp [bernoulliPPressureResidualDiscriminant]
    ring]
  simpa [gaugeAnomalyLeyangBranchPointCandidateAtU1, gaugeAnomalyLeyangDiscriminantAtU1,
    add_comm, add_left_comm, add_assoc, mul_comm, mul_left_comm, mul_assoc] using
    paper_fold_gauge_anomaly_bernoulli_p_leyang_branch_u1 p hp0 hp1

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:fold-bernoulli-p-pressure-discriminant-degree11`. -/
theorem paper_fold_bernoulli_p_pressure_discriminant_degree11 :
    foldBernoulliPPressureDiscriminantDegree11Statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro u p
    dsimp [bernoulliPPressureQuarticDiscriminant, quarticDiscriminant,
      bernoulliPPressureResidualDiscriminant]
    ring
  · intro p
    dsimp [bernoulliPPressureResidualDiscriminant]
    ring
  · exact bernoulliPPressureResidualDiscriminant_u1_eq_zero_iff

end Omega.Folding
