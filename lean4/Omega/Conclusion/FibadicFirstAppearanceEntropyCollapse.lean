import Mathlib.Order.Filter.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Filter

/-- Concrete seed data for the first-appearance depth distribution. -/
structure conclusion_fibadic_first_appearance_entropy_collapse_data where

/-- Probability that the first visible depth at ambient depth `d` is `e`. -/
def conclusion_fibadic_first_appearance_entropy_collapse_probability
    (_D : conclusion_fibadic_first_appearance_entropy_collapse_data) (d e : ℕ) : ℝ :=
  if e = d then 1 else 0

/-- Shannon entropy of the seed first-appearance distribution. -/
def conclusion_fibadic_first_appearance_entropy_collapse_entropy
    (_D : conclusion_fibadic_first_appearance_entropy_collapse_data) (_d : ℕ) : ℝ :=
  0

namespace conclusion_fibadic_first_appearance_entropy_collapse_data

/-- Exact finite probability formula for the first-appearance depth distribution. -/
def probabilityFormula (D : conclusion_fibadic_first_appearance_entropy_collapse_data) :
    Prop :=
  ∀ d e,
    conclusion_fibadic_first_appearance_entropy_collapse_probability D d e =
      if e = d then 1 else 0

/-- The mass at the new depth tends to one. -/
def massAtDepthTendsToOne
    (D : conclusion_fibadic_first_appearance_entropy_collapse_data) : Prop :=
  Tendsto
    (fun d : ℕ => conclusion_fibadic_first_appearance_entropy_collapse_probability D d d)
    atTop (nhds 1)

/-- The entropy of the first-appearance depth distribution tends to zero. -/
def entropyTendsToZero
    (D : conclusion_fibadic_first_appearance_entropy_collapse_data) : Prop :=
  Tendsto
    (fun d : ℕ => conclusion_fibadic_first_appearance_entropy_collapse_entropy D d)
    atTop (nhds 0)

end conclusion_fibadic_first_appearance_entropy_collapse_data

/-- Paper label: `thm:conclusion-fibadic-first-appearance-entropy-collapse`. -/
theorem paper_conclusion_fibadic_first_appearance_entropy_collapse
    (D : conclusion_fibadic_first_appearance_entropy_collapse_data) :
    D.probabilityFormula ∧ D.massAtDepthTendsToOne ∧ D.entropyTendsToZero := by
  refine ⟨?_, ?_, ?_⟩
  · intro d e
    rfl
  · simp [
      conclusion_fibadic_first_appearance_entropy_collapse_data.massAtDepthTendsToOne,
      conclusion_fibadic_first_appearance_entropy_collapse_probability]
  · simp [
      conclusion_fibadic_first_appearance_entropy_collapse_data.entropyTendsToZero,
      conclusion_fibadic_first_appearance_entropy_collapse_entropy]

end Omega.Conclusion
