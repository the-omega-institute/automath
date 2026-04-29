import Mathlib.Algebra.Polynomial.BigOperators
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial

/-- Paper-facing sharp-sampling statement after clearing Laurent denominators by `W^m`. The
cleared certificate is a degree-`≤ 2m` polynomial, so `2m + 1` distinct samples force uniqueness;
conversely, any smaller sample set is annihilated by the product witness `∏ (X - ζ_i)`. -/
def conclusion_finite_laurent_certificate_sharp_sampling_statement (m : ℕ) : Prop :=
  (∀ P Q : ℂ[X], P.natDegree ≤ 2 * m → Q.natDegree ≤ 2 * m →
      ∀ ζ : Fin (2 * m + 1) → ℂ, Function.Injective ζ →
        (∀ i, P.eval (ζ i) = Q.eval (ζ i)) → P = Q) ∧
    ∀ n : ℕ, n ≤ 2 * m → ∀ ζ : Fin n → ℂ,
      ∃ P : ℂ[X], P ≠ 0 ∧ P.natDegree ≤ 2 * m ∧ ∀ i, P.eval (ζ i) = 0

/-- Paper label: `thm:conclusion-finite-laurent-certificate-sharp-sampling`. -/
theorem paper_conclusion_finite_laurent_certificate_sharp_sampling (m : ℕ) :
    conclusion_finite_laurent_certificate_sharp_sampling_statement m := by
  refine ⟨?_, ?_⟩
  · intro P Q hP hQ ζ hζ hEval
    apply Polynomial.eq_of_natDegree_lt_card_of_eval_eq P Q hζ
    · intro i
      simp [hEval i]
    · exact lt_of_le_of_lt (max_le hP hQ) (by
        show 2 * m < Fintype.card (Fin (2 * m + 1))
        simp)
  · intro n hn ζ
    let P : ℂ[X] := Finset.prod (Finset.univ : Finset (Fin n)) fun i => X - C (ζ i)
    refine Exists.intro P ?_
    refine ⟨?_, ?_, ?_⟩
    · exact
        (show P.Monic by
          simp [P, Polynomial.monic_prod_of_monic, Polynomial.monic_X_sub_C]).ne_zero
    · calc
        P.natDegree = n := by
          change
            (Finset.prod (Finset.univ : Finset (Fin n)) (fun i => X - C (ζ i))).natDegree = n
          rw [Polynomial.natDegree_finset_prod_X_sub_C_eq_card]
          simp
        _ ≤ 2 * m := hn
    · intro i
      change
        (Finset.prod (Finset.univ : Finset (Fin n)) (fun j => X - C (ζ j))).eval (ζ i) = 0
      rw [Polynomial.eval_prod, Finset.prod_eq_zero_iff]
      exact ⟨i, by simp, by simp⟩

end Omega.Conclusion
