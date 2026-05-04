import Mathlib.Tactic

namespace Omega.Conclusion

/-- The `Φ₃` factor in the `u`-coordinate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3 (u : ℝ) : ℝ :=
  u ^ 2 + u + 1

/-- The `Φ₄` factor in the `u`-coordinate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4 (u : ℝ) : ℝ :=
  u ^ 2 + 1

/-- The `Φ₅` factor in the `u`-coordinate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5 (u : ℝ) : ℝ :=
  u ^ 4 + u ^ 3 + u ^ 2 + u + 1

/-- The `Φ₆` factor in the `u`-coordinate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6 (u : ℝ) : ℝ :=
  u ^ 2 - u + 1

/-- The denominator clearing constant for the `ρ₄` free-energy certificate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4 : ℕ := 240

/-- The denominator clearing constant for the `ρ₅` free-energy certificate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5 : ℕ := 300

/-- The denominator clearing constant for the `ρ₆` free-energy certificate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6 : ℕ := 180

lemma conclusion_leyang_rho456_positive_axis_singularity_exclusion_u_plus_one_ne
    {u : ℝ} (hu : 0 < u) : u + 1 ≠ 0 := by
  linarith

lemma conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3_pos
    {u : ℝ} (hu : 0 < u) :
    0 < conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3 u := by
  unfold conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3
  nlinarith [sq_nonneg u]

lemma conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4_pos
    (u : ℝ) :
    0 < conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4 u := by
  unfold conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4
  nlinarith [sq_nonneg u]

lemma conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5_pos
    {u : ℝ} (hu : 0 < u) :
    0 < conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5 u := by
  unfold conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5
  have h2 : 0 ≤ u ^ 2 := by positivity
  have h3 : 0 ≤ u ^ 3 := by positivity
  have h4 : 0 ≤ u ^ 4 := by positivity
  nlinarith

lemma conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6_pos
    (u : ℝ) :
    0 < conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6 u := by
  unfold conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6
  nlinarith [sq_nonneg (u - (1 / 2 : ℝ))]

/-- The non-`u - 1` cyclotomic factors have no positive-real zero. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_cyclotomicSafe
    (u : ℝ) : Prop :=
  u + 1 ≠ 0 ∧
    conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3 u ≠ 0 ∧
    conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4 u ≠ 0 ∧
    conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5 u ≠ 0 ∧
    conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6 u ≠ 0

/-- Concrete positive-axis singularity-exclusion and denominator-clearing certificate. -/
def conclusion_leyang_rho456_positive_axis_singularity_exclusion_statement : Prop :=
  (∀ u : ℝ, 0 < u → u ≠ 1 →
    u - 1 ≠ 0 ∧
      conclusion_leyang_rho456_positive_axis_singularity_exclusion_cyclotomicSafe u) ∧
  conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4 = 240 ∧
  conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5 = 300 ∧
  conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6 = 180 ∧
  (24 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4 ∧
    30 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4 ∧
    40 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4) ∧
  (30 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5 ∧
    60 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5 ∧
    100 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5) ∧
  (18 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6 ∧
    30 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6 ∧
    36 ∣ conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6)

/-- Paper label: `thm:conclusion-leyang-rho456-positive-axis-singularity-exclusion`. -/
theorem paper_conclusion_leyang_rho456_positive_axis_singularity_exclusion :
    conclusion_leyang_rho456_positive_axis_singularity_exclusion_statement := by
  refine ⟨?_, rfl, rfl, rfl, ?_, ?_, ?_⟩
  · intro u hu hu_ne_one
    refine ⟨sub_ne_zero.mpr hu_ne_one, ?_⟩
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact conclusion_leyang_rho456_positive_axis_singularity_exclusion_u_plus_one_ne hu
    · exact ne_of_gt
        (conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi3_pos hu)
    · exact ne_of_gt
        (conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi4_pos u)
    · exact ne_of_gt
        (conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi5_pos hu)
    · exact ne_of_gt
        (conclusion_leyang_rho456_positive_axis_singularity_exclusion_phi6_pos u)
  · norm_num [conclusion_leyang_rho456_positive_axis_singularity_exclusion_D4]
  · norm_num [conclusion_leyang_rho456_positive_axis_singularity_exclusion_D5]
  · norm_num [conclusion_leyang_rho456_positive_axis_singularity_exclusion_D6]

end Omega.Conclusion
