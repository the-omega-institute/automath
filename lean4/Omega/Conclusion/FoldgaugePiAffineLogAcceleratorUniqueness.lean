import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- A fixed finite-window affine-log certificate, represented by its annihilating polynomial. -/
abbrev conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_certificate :=
  Polynomial ℚ

/-- Interpolation data for the prefixed finite-window certificate. -/
def conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_condition
    (R : ℕ) (ρ : Fin R → ℚ)
    (P : conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_certificate) : Prop :=
  P.natDegree ≤ R ∧ P.eval 1 = 1 ∧ ∀ i : Fin R, P.eval (ρ i) = 0

/-- Generic finite-window uniqueness and short-window obstruction statement. -/
def conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_statement (R : ℕ) : Prop :=
  (∀ ρ : Fin R → ℚ, Function.Injective ρ → (∀ i : Fin R, ρ i ≠ 1) →
    ∀ P Q : conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_certificate,
      conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_condition R ρ P →
        conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_condition R ρ Q →
          P = Q) ∧
    ∀ M : ℕ, M < R →
      ∀ ρ : Fin R → ℚ, Function.Injective ρ → (∀ i : Fin R, ρ i ≠ 1) →
        ∀ P : conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_certificate,
          P.natDegree ≤ M → P.eval 1 = 1 → ¬ (∀ i : Fin R, P.eval (ρ i) = 0)

lemma conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_augmented_injective
    {R : ℕ} {ρ : Fin R → ℚ} (hρ : Function.Injective ρ)
    (hρ1 : ∀ i : Fin R, ρ i ≠ 1) :
    Function.Injective (fun i : Fin (R + 1) =>
      if h : (i : ℕ) = 0 then (1 : ℚ)
      else ρ ⟨i - 1, by omega⟩) := by
  intro i j hij
  by_cases hi : (i : ℕ) = 0
  · by_cases hj : (j : ℕ) = 0
    · exact Fin.ext (by omega)
    · have hval : (1 : ℚ) = ρ ⟨j - 1, by omega⟩ := by simpa [hi, hj] using hij
      exact False.elim (hρ1 ⟨j - 1, by omega⟩ hval.symm)
  · by_cases hj : (j : ℕ) = 0
    · have hval : ρ ⟨i - 1, by omega⟩ = (1 : ℚ) := by simpa [hi, hj] using hij
      exact False.elim (hρ1 ⟨i - 1, by omega⟩ hval)
    · have hpre : (⟨i - 1, by omega⟩ : Fin R) = ⟨j - 1, by omega⟩ := by
        apply hρ
        simpa [hi, hj] using hij
      have hpreVal : i.1 - 1 = j.1 - 1 := by
        have := congrArg Fin.val hpre
        simpa using this
      exact Fin.ext (by omega)

/-- Paper label: `thm:conclusion-foldgauge-pi-affine-log-accelerator-uniqueness`. -/
theorem paper_conclusion_foldgauge_pi_affine_log_accelerator_uniqueness
    (R : ℕ) (hR : 1 ≤ R) :
    conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_statement R := by
  refine ⟨?_, ?_⟩
  · intro ρ hρ hρ1 P Q hP hQ
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q
      (conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_augmented_injective hρ hρ1)
    · intro i
      by_cases hi : (i : ℕ) = 0
      · simpa [hi,
          conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_condition] using
          hP.2.1.trans hQ.2.1.symm
      · simpa [hi,
          conclusion_foldgauge_pi_affine_log_accelerator_uniqueness_condition] using
          (hP.2.2 ⟨i - 1, by omega⟩).trans (hQ.2.2 ⟨i - 1, by omega⟩).symm
    · have hdeg : max P.natDegree Q.natDegree ≤ R := max_le hP.1 hQ.1
      exact lt_of_le_of_lt hdeg (by simp)
  · intro M hM ρ hρ hρ1 P hdeg hnorm hroots
    have hzero : P = 0 := by
      apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero P hρ hroots
      exact lt_of_le_of_lt hdeg (by simpa using hM)
    simp [hzero] at hnorm

end Omega.Conclusion
