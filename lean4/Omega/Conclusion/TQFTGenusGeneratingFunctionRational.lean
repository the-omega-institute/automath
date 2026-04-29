import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic
import Omega.Conclusion.TQFTGenusLinearRecurrenceRecovery
import Omega.Conclusion.TqftGenusLogconvexity

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

section TQFTGenusGeneratingFunctionRational

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The geometric-series summand attached to a single multiplicity value. -/
def conclusion_tqft_genus_generating_function_rational_geometricSummand
    (d : X → Nat) (x : X) (z : ℚ) : ℚ :=
  ((d x : ℚ) ^ 2) / (1 - z / ((d x : ℚ) ^ 2))

/-- The same summand rewritten with denominator `d(x)^2 - z`. -/
def conclusion_tqft_genus_generating_function_rational_resolventSummand
    (d : X → Nat) (x : X) (z : ℚ) : ℚ :=
  ((d x : ℚ) ^ 4) / (((d x : ℚ) ^ 2) - z)

/-- The chapter-local genus generating function as a finite sum of geometric summands. -/
def conclusion_tqft_genus_generating_function_rational_series
    (d : X → Nat) (z : ℚ) : ℚ :=
  ∑ x, conclusion_tqft_genus_generating_function_rational_geometricSummand d x z

/-- Finite pole-support candidate set, given by the squared multiplicity values. -/
def conclusion_tqft_genus_generating_function_rational_poleSupport
    (d : X → Nat) : Finset ℚ :=
  Finset.univ.image fun x => (d x : ℚ) ^ 2

/-- Concrete genus-generating-function package: the series is already a finite sum of geometric
series, it has the equivalent resolvent form, and the finite pole-support set is exactly the image
of the squared multiplicity values. -/
def conclusion_tqft_genus_generating_function_rational_statement (d : X → Nat) : Prop :=
  (∀ z,
    conclusion_tqft_genus_generating_function_rational_series d z =
      ∑ x, conclusion_tqft_genus_generating_function_rational_geometricSummand d x z) ∧
    (∀ z,
      conclusion_tqft_genus_generating_function_rational_series d z =
        ∑ x, conclusion_tqft_genus_generating_function_rational_resolventSummand d x z) ∧
    ∀ q : ℚ,
      q ∈ conclusion_tqft_genus_generating_function_rational_poleSupport d ↔
        ∃ x : X, (d x : ℚ) ^ 2 = q

omit [Fintype X] [DecidableEq X] in
lemma conclusion_tqft_genus_generating_function_rational_summand_eq
    (d : X → Nat) (x : X) (z : ℚ) :
    conclusion_tqft_genus_generating_function_rational_geometricSummand d x z =
      conclusion_tqft_genus_generating_function_rational_resolventSummand d x z := by
  by_cases hsq : ((d x : ℚ) ^ 2) = 0
  · have hx0 : (d x : ℚ) = 0 := by
      exact eq_zero_of_pow_eq_zero hsq
    simp [conclusion_tqft_genus_generating_function_rational_geometricSummand,
      conclusion_tqft_genus_generating_function_rational_resolventSummand, hx0]
  · let a : ℚ := (d x : ℚ) ^ 2
    have ha : a ≠ 0 := by
      simpa [a] using hsq
    have hrewrite : 1 - z / a = (a - z) / a := by
      field_simp [ha]
    calc
      conclusion_tqft_genus_generating_function_rational_geometricSummand d x z
          = a / (1 - z / a) := by
              simp [conclusion_tqft_genus_generating_function_rational_geometricSummand, a]
      _ = a / ((a - z) / a) := by rw [hrewrite]
      _ = a * a / (a - z) := by
            field_simp [ha]
      _ = a ^ 2 / (a - z) := by ring
      _ = conclusion_tqft_genus_generating_function_rational_resolventSummand d x z := by
            simp [conclusion_tqft_genus_generating_function_rational_resolventSummand, a]
            congr 1
            ring

/-- Paper label: `prop:conclusion-tqft-genus-generating-function-rational`. -/
theorem paper_conclusion_tqft_genus_generating_function_rational {X : Type} [Fintype X]
    [DecidableEq X] (d : X → Nat) :
    conclusion_tqft_genus_generating_function_rational_statement d := by
  refine ⟨?_, ?_, ?_⟩
  · intro z
    rfl
  · intro z
    unfold conclusion_tqft_genus_generating_function_rational_series
    refine Finset.sum_congr rfl ?_
    intro x hx
    exact conclusion_tqft_genus_generating_function_rational_summand_eq d x z
  · intro q
    constructor
    · intro hq
      rcases Finset.mem_image.mp hq with ⟨x, -, hx⟩
      exact ⟨x, hx⟩
    · rintro ⟨x, rfl⟩
      exact Finset.mem_image.mpr ⟨x, by simp, rfl⟩

end TQFTGenusGeneratingFunctionRational

end

end Omega.Conclusion
