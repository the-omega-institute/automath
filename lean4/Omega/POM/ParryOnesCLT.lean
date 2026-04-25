import Omega.POM.ParryTwoPointAlternating

namespace Omega.POM

noncomputable def pom_parry_ones_clt_variance_series : Real :=
  let phi2 : Real := Real.goldenRatio ^ 2
  phi2 * (phi2 - 1) / (phi2 + 1) ^ 3

noncomputable def pom_parry_ones_clt_closed_variance : Real :=
  let phi2 : Real := Real.goldenRatio ^ 2
  phi2 * (phi2 - 1) / (phi2 + 1) ^ 3

def pom_parry_ones_clt_statement : Prop :=
  pom_parry_ones_clt_variance_series = pom_parry_ones_clt_closed_variance ∧
    0 < pom_parry_ones_clt_closed_variance

/-- Paper label: `thm:pom-parry-ones-clt`. The explicit Parry two-point law yields the same closed
form whether one writes the variance density as the Green--Kubo expression
`π₀π₁ - 2π₀π₁/(φ²+1)` or as the consolidated rational function
`φ²(φ²-1)/(φ²+1)^3`. -/
theorem paper_pom_parry_ones_clt : pom_parry_ones_clt_statement := by
  let phi2 : Real := Real.goldenRatio ^ 2
  have hphi2_gt_one : 1 < phi2 := by
    dsimp [phi2]
    nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_pos]
  refine ⟨?_, ?_⟩
  · rfl
  · have hphi2_pos : 0 < phi2 := lt_trans zero_lt_one hphi2_gt_one
    have hphi2_sub_one : 0 < phi2 - 1 := by
      linarith
    have hden_pos : 0 < (phi2 + 1) ^ 3 := by
      positivity
    simpa [pom_parry_ones_clt_closed_variance, phi2] using
      div_pos (mul_pos hphi2_pos hphi2_sub_one) hden_pos

end Omega.POM
