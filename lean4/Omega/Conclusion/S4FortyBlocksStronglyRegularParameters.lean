import Mathlib.Tactic

namespace Omega.Conclusion

/-- The number of blocks in the rank-`3` action. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_v : ℕ := 40

/-- The valency of the nontrivial suborbit graph of size `12`. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_k : ℕ := 12

/-- The unique strongly regular `λ` parameter under the rank-`3` arithmetic constraints. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda : ℕ := 2

/-- The unique strongly regular `μ` parameter under the rank-`3` arithmetic constraints. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu : ℕ := 4

/-- The positive nontrivial eigenvalue. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_r : ℤ := 2

/-- The negative nontrivial eigenvalue. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_s : ℤ := -4

/-- Multiplicity of the eigenvalue `2`. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_r : ℕ := 24

/-- Multiplicity of the eigenvalue `-4`. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_s : ℕ := 15

/-- Paper-facing arithmetic package for
`thm:conclusion-s4-40blocks-rank3-strongly-regular-parameters`. -/
def conclusion_s4_40blocks_rank3_strongly_regular_parameters_statement : Prop :=
  conclusion_s4_40blocks_rank3_strongly_regular_parameters_v = 40 ∧
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_k = 12 ∧
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda = 2 ∧
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu = 4 ∧
    (∀ lambda mu : ℕ,
      lambda < conclusion_s4_40blocks_rank3_strongly_regular_parameters_k →
        mu ≤ conclusion_s4_40blocks_rank3_strongly_regular_parameters_k →
        4 * lambda + 9 * mu = 44 →
        mu ≠ 0 →
        lambda = conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda ∧
          mu = conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu) ∧
    (conclusion_s4_40blocks_rank3_strongly_regular_parameters_r ^ 2 +
        ((conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu : ℤ) -
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda) *
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_r +
        ((conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu : ℤ) -
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_k) = 0) ∧
    (conclusion_s4_40blocks_rank3_strongly_regular_parameters_s ^ 2 +
        ((conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu : ℤ) -
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda) *
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_s +
        ((conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu : ℤ) -
          conclusion_s4_40blocks_rank3_strongly_regular_parameters_k) = 0) ∧
    1 + conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_r +
        conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_s =
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_v ∧
    (12 : ℤ) + conclusion_s4_40blocks_rank3_strongly_regular_parameters_r *
        conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_r -
        4 * conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_s = 0

lemma conclusion_s4_40blocks_rank3_strongly_regular_parameters_unique
    (lambda mu : ℕ)
    (hlambda : lambda < conclusion_s4_40blocks_rank3_strongly_regular_parameters_k)
    (_hmu : mu ≤ conclusion_s4_40blocks_rank3_strongly_regular_parameters_k)
    (harith : 4 * lambda + 9 * mu = 44)
    (hmu_nonzero : mu ≠ 0) :
    lambda = conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda ∧
      mu = conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu := by
  unfold conclusion_s4_40blocks_rank3_strongly_regular_parameters_k at hlambda
  unfold conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu
  omega

/-- Paper label: `thm:conclusion-s4-40blocks-rank3-strongly-regular-parameters`. -/
theorem paper_conclusion_s4_40blocks_rank3_strongly_regular_parameters :
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_statement := by
  unfold conclusion_s4_40blocks_rank3_strongly_regular_parameters_statement
  refine ⟨rfl, rfl, rfl, rfl,
    conclusion_s4_40blocks_rank3_strongly_regular_parameters_unique, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_s4_40blocks_rank3_strongly_regular_parameters_r,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_k]
  · norm_num [conclusion_s4_40blocks_rank3_strongly_regular_parameters_s,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_mu,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_lambda,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_k]
  · norm_num [conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_r,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_s,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_v]
  · norm_num [conclusion_s4_40blocks_rank3_strongly_regular_parameters_r,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_r,
      conclusion_s4_40blocks_rank3_strongly_regular_parameters_m_s]

end Omega.Conclusion
