import Mathlib.Tactic

namespace Omega.POM

noncomputable section

/-- The normalized conditional Chernoff curve used for the secant-law wrapper. -/
def pom_fiber_chernoff_secant_law_unique_maximizer_curve (s : ℝ) : ℝ :=
  s * (1 - s)

/-- The secant slope of the normalized conditional Chernoff curve. -/
def pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope (u v : ℝ) : ℝ :=
  (pom_fiber_chernoff_secant_law_unique_maximizer_curve v -
      pom_fiber_chernoff_secant_law_unique_maximizer_curve u) / (v - u)

/-- The complete prefixed statement: the quadratic Chernoff curve obeys the secant mean law and
has the unique maximizer `1 / 2` on the compact unit interval. -/
def pom_fiber_chernoff_secant_law_unique_maximizer_statement : Prop :=
  (∀ u v : ℝ, u < v →
    pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope u v = 1 - (u + v)) ∧
    (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      pom_fiber_chernoff_secant_law_unique_maximizer_curve s ≤
        pom_fiber_chernoff_secant_law_unique_maximizer_curve (1 / 2)) ∧
    (∀ s ∈ Set.Icc (0 : ℝ) 1,
      pom_fiber_chernoff_secant_law_unique_maximizer_curve s =
          pom_fiber_chernoff_secant_law_unique_maximizer_curve (1 / 2) →
        s = 1 / 2) ∧
    pom_fiber_chernoff_secant_law_unique_maximizer_curve (1 / 2) = 1 / 4

lemma pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak (s : ℝ) :
    pom_fiber_chernoff_secant_law_unique_maximizer_curve s =
      1 / 4 - (s - 1 / 2) ^ 2 := by
  unfold pom_fiber_chernoff_secant_law_unique_maximizer_curve
  ring

lemma pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope_eq (u v : ℝ)
    (huv : u < v) :
    pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope u v = 1 - (u + v) := by
  have hne : v - u ≠ 0 := sub_ne_zero.mpr (ne_of_gt huv)
  unfold pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope
    pom_fiber_chernoff_secant_law_unique_maximizer_curve
  field_simp [hne]
  ring

/-- Paper label: `thm:pom-fiber-chernoff-secant-law-unique-maximizer`. -/
theorem paper_pom_fiber_chernoff_secant_law_unique_maximizer :
    pom_fiber_chernoff_secant_law_unique_maximizer_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro u v huv
    exact pom_fiber_chernoff_secant_law_unique_maximizer_secantSlope_eq u v huv
  · norm_num
  · intro s _hs
    rw [pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak,
      pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak]
    nlinarith [sq_nonneg (s - 1 / 2)]
  · intro s _hs hmax
    rw [pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak,
      pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak] at hmax
    nlinarith [sq_nonneg (s - 1 / 2)]
  · rw [pom_fiber_chernoff_secant_law_unique_maximizer_curve_peak]
    ring

end

end Omega.POM
