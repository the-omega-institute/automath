import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Conclusion.BinfoldTwoScalarCompleteReconstruction

namespace Omega.Conclusion

noncomputable section

/-- The Bernoulli weight from the bin-fold escort limit family at the golden parameter. -/
def conclusion_binfold_escort_sqrt_circle_arc_theta (q : ℕ) : ℝ :=
  binfoldEscortTheta Real.goldenRatio q

/-- The square-root coordinate `u = φ^{-((q + 1) / 2)}` realized as `sqrt (φ^{-(q + 1)})`. -/
def conclusion_binfold_escort_sqrt_circle_arc_u (q : ℕ) : ℝ :=
  Real.sqrt (1 / Real.goldenRatio ^ (q + 1))

/-- The square-root embedding of the Bernoulli escort family into the positive unit circle. -/
def conclusion_binfold_escort_sqrt_circle_arc_Xi (q : ℕ) : ℝ × ℝ :=
  (Real.sqrt (1 - conclusion_binfold_escort_sqrt_circle_arc_theta q),
    Real.sqrt (conclusion_binfold_escort_sqrt_circle_arc_theta q))

/-- The arclength parameter on the positive unit circle. -/
def conclusion_binfold_escort_sqrt_circle_arc_alpha (q : ℕ) : ℝ :=
  Real.arctan (conclusion_binfold_escort_sqrt_circle_arc_u q)

lemma conclusion_binfold_escort_sqrt_circle_arc_u_sq (q : ℕ) :
    conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2 = 1 / Real.goldenRatio ^ (q + 1) := by
  unfold conclusion_binfold_escort_sqrt_circle_arc_u
  rw [Real.sq_sqrt]
  positivity

lemma conclusion_binfold_escort_sqrt_circle_arc_theta_rewrite (q : ℕ) :
    conclusion_binfold_escort_sqrt_circle_arc_theta q =
      conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2 /
        (1 + conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2) := by
  have hpow_ne : (Real.goldenRatio ^ (q + 1) : ℝ) ≠ 0 := by
    positivity
  rw [conclusion_binfold_escort_sqrt_circle_arc_u_sq]
  unfold conclusion_binfold_escort_sqrt_circle_arc_theta binfoldEscortTheta
  field_simp [hpow_ne]
  ring

lemma conclusion_binfold_escort_sqrt_circle_arc_one_sub_theta_rewrite (q : ℕ) :
    1 - conclusion_binfold_escort_sqrt_circle_arc_theta q =
      1 / (1 + conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2) := by
  rw [conclusion_binfold_escort_sqrt_circle_arc_theta_rewrite]
  field_simp
  ring

theorem conclusion_binfold_escort_sqrt_circle_arc_Xi_eq (q : ℕ) :
    conclusion_binfold_escort_sqrt_circle_arc_Xi q =
      (Real.cos (conclusion_binfold_escort_sqrt_circle_arc_alpha q),
        Real.sin (conclusion_binfold_escort_sqrt_circle_arc_alpha q)) := by
  have hu_nonneg : 0 ≤ conclusion_binfold_escort_sqrt_circle_arc_u q := by
    unfold conclusion_binfold_escort_sqrt_circle_arc_u
    exact Real.sqrt_nonneg _
  have hcos :
      Real.sqrt (1 - conclusion_binfold_escort_sqrt_circle_arc_theta q) =
        Real.cos (conclusion_binfold_escort_sqrt_circle_arc_alpha q) := by
    rw [conclusion_binfold_escort_sqrt_circle_arc_one_sub_theta_rewrite]
    unfold conclusion_binfold_escort_sqrt_circle_arc_alpha
    rw [show 1 / (1 + conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2) =
        (1 + conclusion_binfold_escort_sqrt_circle_arc_u q ^ 2)⁻¹ by field_simp,
      Real.sqrt_inv, Real.cos_arctan]
    simp [one_div]
  have hsin :
      Real.sqrt (conclusion_binfold_escort_sqrt_circle_arc_theta q) =
        Real.sin (conclusion_binfold_escort_sqrt_circle_arc_alpha q) := by
    rw [conclusion_binfold_escort_sqrt_circle_arc_theta_rewrite]
    unfold conclusion_binfold_escort_sqrt_circle_arc_alpha
    rw [Real.sqrt_div (sq_nonneg _), Real.sqrt_sq hu_nonneg, Real.sin_arctan]
  ext <;> simp [conclusion_binfold_escort_sqrt_circle_arc_Xi, hcos, hsin]

/-- Paper label: `cor:conclusion-binfold-escort-sqrt-circle-arc`. -/
theorem paper_conclusion_binfold_escort_sqrt_circle_arc :
    ∀ q : ℕ,
      conclusion_binfold_escort_sqrt_circle_arc_Xi q =
        (Real.cos (conclusion_binfold_escort_sqrt_circle_arc_alpha q),
          Real.sin (conclusion_binfold_escort_sqrt_circle_arc_alpha q)) := by
  intro q
  exact conclusion_binfold_escort_sqrt_circle_arc_Xi_eq q

end

end Omega.Conclusion
