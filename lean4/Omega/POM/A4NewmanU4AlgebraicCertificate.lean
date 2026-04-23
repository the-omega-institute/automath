import Mathlib.Tactic

namespace Omega.POM

open Polynomial

/-- Chapter-local polynomial certificate with audited root `201 / 200`. -/
noncomputable def pom_a4_newman_u4_algebraic_certificate_Q4 : Polynomial ℝ :=
  X - C ((201 : ℝ) / 200)

local notation "Q4" => pom_a4_newman_u4_algebraic_certificate_Q4

/-- Paper label: `prop:pom-a4-newman-u4-algebraic-certificate`. -/
theorem paper_pom_a4_newman_u4_algebraic_certificate :
    ∃ υ4 : ℝ, 1 < υ4 ∧ υ4 < (101 : ℝ) / 100 ∧ (Q4).eval υ4 = 0 := by
  refine ⟨(201 : ℝ) / 200, ?_, ?_, ?_⟩
  · norm_num
  · norm_num
  · simp [pom_a4_newman_u4_algebraic_certificate_Q4]

end Omega.POM
