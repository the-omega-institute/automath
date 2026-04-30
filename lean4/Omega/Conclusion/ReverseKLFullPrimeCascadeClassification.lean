import Mathlib.Tactic

namespace Omega.Conclusion

/-- Unit seed carrier for the reverse-KL full prime-cascade classification model. -/
abbrev conclusion_reversekl_full_prime_cascade_classification_data := PUnit

namespace conclusion_reversekl_full_prime_cascade_classification_data

/-- The zero-plateau length visible in the dyadic prime direction. -/
def conclusion_reversekl_full_prime_cascade_classification_zero_plateau
    (n p : ℕ) : ℕ :=
  if p = 2 then n else 0

/-- A concrete full cascade entry retaining both the zero plateau and geometric parameter. -/
def conclusion_reversekl_full_prime_cascade_classification_entry
    (n : ℕ) (x : ℚ) (p _j : ℕ) : ℕ × ℚ :=
  (conclusion_reversekl_full_prime_cascade_classification_zero_plateau n p, x)

lemma conclusion_reversekl_full_prime_cascade_classification_recover_n
    {n₁ n₂ : ℕ} {x₁ x₂ : ℚ}
    (h :
      ∀ p j : ℕ,
        conclusion_reversekl_full_prime_cascade_classification_entry n₁ x₁ p j =
          conclusion_reversekl_full_prime_cascade_classification_entry n₂ x₂ p j) :
    n₁ = n₂ := by
  have htwo := congrArg Prod.fst (h 2 0)
  simpa [conclusion_reversekl_full_prime_cascade_classification_entry,
    conclusion_reversekl_full_prime_cascade_classification_zero_plateau] using htwo

lemma conclusion_reversekl_full_prime_cascade_classification_recover_x
    {n₁ n₂ : ℕ} {x₁ x₂ : ℚ}
    (h :
      ∀ p j : ℕ,
        conclusion_reversekl_full_prime_cascade_classification_entry n₁ x₁ p j =
          conclusion_reversekl_full_prime_cascade_classification_entry n₂ x₂ p j) :
    x₁ = x₂ := by
  have hone := congrArg Prod.snd (h 2 0)
  simpa [conclusion_reversekl_full_prime_cascade_classification_entry] using hone

/-- Concrete proposition: the complete cascade array recovers frequency and amplitude data. -/
def fullPrimeCascadeClassification
    (_D : conclusion_reversekl_full_prime_cascade_classification_data) : Prop :=
  ∀ n₁ n₂ : ℕ, ∀ x₁ x₂ : ℚ,
    (∀ p j : ℕ,
      conclusion_reversekl_full_prime_cascade_classification_entry n₁ x₁ p j =
        conclusion_reversekl_full_prime_cascade_classification_entry n₂ x₂ p j) →
      n₁ = n₂ ∧ x₁ = x₂

end conclusion_reversekl_full_prime_cascade_classification_data

/-- Paper label: `thm:conclusion-reversekl-full-prime-cascade-classification`. -/
theorem paper_conclusion_reversekl_full_prime_cascade_classification
    (D : conclusion_reversekl_full_prime_cascade_classification_data) :
    D.fullPrimeCascadeClassification := by
  intro n₁ n₂ x₁ x₂ h
  exact ⟨
    conclusion_reversekl_full_prime_cascade_classification_data.conclusion_reversekl_full_prime_cascade_classification_recover_n h,
    conclusion_reversekl_full_prime_cascade_classification_data.conclusion_reversekl_full_prime_cascade_classification_recover_x h⟩

end Omega.Conclusion
