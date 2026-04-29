import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Concrete seed object for the binary Gödel logistic common-support model. -/
abbrev conclusion_binary_godel_logistic_common_support_singularity_data := PUnit

/-- The symbolic binary address map used by the coding model. -/
def conclusion_binary_godel_logistic_common_support_singularity_address
    (ω : ℕ → Bool) : ℕ → Bool :=
  ω

/-- A normalized decreasing logistic address parameter. -/
def conclusion_binary_godel_logistic_common_support_singularity_theta (q : ℕ) : ℝ :=
  1 / (((q + 2 : ℕ) : ℝ))

/-- The full symbolic support before coding. -/
def conclusion_binary_godel_logistic_common_support_singularity_fullSupport :
    Set (ℕ → Bool) :=
  Set.univ

/-- The coded support of the binary address map. -/
def conclusion_binary_godel_logistic_common_support_singularity_codedSupport :
    Set (ℕ → Bool) :=
  Set.range conclusion_binary_godel_logistic_common_support_singularity_address

/-- Paper-facing concrete statement for common support and parameter separation. -/
def conclusion_binary_godel_logistic_common_support_singularity_statement
    (_D : conclusion_binary_godel_logistic_common_support_singularity_data) : Prop :=
  Function.Injective conclusion_binary_godel_logistic_common_support_singularity_address ∧
    StrictAnti conclusion_binary_godel_logistic_common_support_singularity_theta ∧
      0 < conclusion_binary_godel_logistic_common_support_singularity_theta 0 ∧
        conclusion_binary_godel_logistic_common_support_singularity_theta 0 < 1 ∧
          conclusion_binary_godel_logistic_common_support_singularity_theta 0 ≠
            conclusion_binary_godel_logistic_common_support_singularity_theta 1 ∧
            conclusion_binary_godel_logistic_common_support_singularity_codedSupport =
              conclusion_binary_godel_logistic_common_support_singularity_fullSupport

/-- Paper label: `thm:conclusion-binary-godel-logistic-common-support-singularity`. -/
theorem paper_conclusion_binary_godel_logistic_common_support_singularity
    (D : conclusion_binary_godel_logistic_common_support_singularity_data) :
    conclusion_binary_godel_logistic_common_support_singularity_statement D := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω η h
    exact h
  · intro p q hpq
    unfold conclusion_binary_godel_logistic_common_support_singularity_theta
    have hpos : (0 : ℝ) < ((p + 2 : ℕ) : ℝ) := by positivity
    have hlt : ((p + 2 : ℕ) : ℝ) < ((q + 2 : ℕ) : ℝ) := by
      exact_mod_cast Nat.add_lt_add_right hpq 2
    exact one_div_lt_one_div_of_lt hpos hlt
  · norm_num [conclusion_binary_godel_logistic_common_support_singularity_theta]
  · norm_num [conclusion_binary_godel_logistic_common_support_singularity_theta]
  · norm_num [conclusion_binary_godel_logistic_common_support_singularity_theta]
  · ext ω
    constructor
    · intro _h
      trivial
    · intro _h
      exact ⟨ω, rfl⟩

end

end Omega.Conclusion
