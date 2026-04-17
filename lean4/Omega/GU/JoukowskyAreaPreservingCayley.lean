import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Tactic

namespace Omega.GU

/-- Area-preserving normalization of the major semiaxis. -/
noncomputable def normalizedMajorSemiaxis (u : ℝ) : ℝ :=
  Real.exp u

/-- Area-preserving normalization of the minor semiaxis. -/
noncomputable def normalizedMinorSemiaxis (u : ℝ) : ℝ :=
  Real.exp (-u)

/-- Cayley parameter attached to the normalized Joukowsky ellipse. -/
noncomputable def joukowskyCayleyParameter (u : ℝ) : ℝ :=
  (Real.exp u - 1) / (Real.exp u + 1)

/-- Einstein addition law on the Cayley parameter. -/
noncomputable def einsteinAdd (x y : ℝ) : ℝ :=
  (x + y) / (1 + x * y)

/-- The normalized semiaxes are reciprocal and admit the usual hyperbolic parametrization. -/
def normalizedFamily (u : ℝ) : Prop :=
  normalizedMajorSemiaxis u * normalizedMinorSemiaxis u = 1 ∧
    normalizedMajorSemiaxis u + normalizedMinorSemiaxis u = 2 * Real.cosh u ∧
    normalizedMajorSemiaxis u - normalizedMinorSemiaxis u = 2 * Real.sinh u

/-- Cayley composition law for the normalized Joukowsky parameter. -/
noncomputable def cayleyComposition (u v : ℝ) : Prop :=
  joukowskyCayleyParameter (u + v) =
    (joukowskyCayleyParameter u + joukowskyCayleyParameter v) /
      (1 + joukowskyCayleyParameter u * joukowskyCayleyParameter v)

/-- Einstein-addition form of the same Cayley composition law. -/
noncomputable def einsteinAddition (u v : ℝ) : Prop :=
  joukowskyCayleyParameter (u + v) =
    einsteinAdd (joukowskyCayleyParameter u) (joukowskyCayleyParameter v)

lemma normalizedFamily_exp_hyperbolic (u : ℝ) : normalizedFamily u := by
  unfold normalizedFamily normalizedMajorSemiaxis normalizedMinorSemiaxis
  refine ⟨?_, ?_, ?_⟩
  · rw [← Real.exp_add]
    ring_nf
    simp
  · rw [Real.cosh_eq, Real.exp_neg]
    ring
  · rw [Real.sinh_eq, Real.exp_neg]
    ring

lemma cayleyParameter_num (u v : ℝ) :
    joukowskyCayleyParameter u + joukowskyCayleyParameter v =
      (2 * (Real.exp u * Real.exp v - 1)) / ((Real.exp u + 1) * (Real.exp v + 1)) := by
  unfold joukowskyCayleyParameter
  have hu : Real.exp u + 1 ≠ 0 := by positivity
  have hv : Real.exp v + 1 ≠ 0 := by positivity
  field_simp [hu, hv]
  ring

lemma cayleyParameter_den (u v : ℝ) :
    1 + joukowskyCayleyParameter u * joukowskyCayleyParameter v =
      (2 * (Real.exp u * Real.exp v + 1)) / ((Real.exp u + 1) * (Real.exp v + 1)) := by
  unfold joukowskyCayleyParameter
  have hu : Real.exp u + 1 ≠ 0 := by positivity
  have hv : Real.exp v + 1 ≠ 0 := by positivity
  field_simp [hu, hv]
  ring

lemma cayleyComposition_exp (u v : ℝ) : cayleyComposition u v := by
  unfold cayleyComposition
  rw [cayleyParameter_num, cayleyParameter_den]
  rw [joukowskyCayleyParameter, Real.exp_add]
  have hu : Real.exp u + 1 ≠ 0 := by positivity
  have hv : Real.exp v + 1 ≠ 0 := by positivity
  have huv : Real.exp u * Real.exp v + 1 ≠ 0 := by positivity
  field_simp [hu, hv, huv]

/-- Area-preserving Joukowsky normalization gives reciprocal semiaxes, the hyperbolic
parametrization, and the Cayley/Einstein composition law on the normalized parameter.
    thm:group-jg-joukowsky-area-preserving-cayley -/
theorem paper_group_jg_joukowsky_area_preserving_cayley (u v : ℝ) :
    normalizedFamily u ∧ cayleyComposition u v ∧ einsteinAddition u v := by
  refine ⟨normalizedFamily_exp_hyperbolic u, cayleyComposition_exp u v, ?_⟩
  simpa [einsteinAddition, einsteinAdd, cayleyComposition] using cayleyComposition_exp u v

end Omega.GU
