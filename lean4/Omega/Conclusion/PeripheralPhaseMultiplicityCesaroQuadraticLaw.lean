import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Finset
open scoped BigOperators

noncomputable section

def conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_cesaroMean
    {L J : ℕ} (phase : Fin J → Fin L) (χ : Fin L → Fin L → ℂ) : ℂ :=
  (1 / (L : ℂ)) *
    ∑ q : Fin L, (∑ i : Fin J, χ (phase i) q) * (∑ j : Fin J, (χ (phase j) q)⁻¹)

def conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_multiplicity
    {L J : ℕ} (phase : Fin J → Fin L) (a : Fin L) : ℂ :=
  ∑ i : Fin J, if phase i = a then 1 else 0

def conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum
    {L J : ℕ} (phase : Fin J → Fin L) : ℂ :=
  ∑ a : Fin L,
    conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_multiplicity phase a ^ 2

def conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_statement : Prop :=
  ∀ {L J : ℕ} [NeZero L] (phase : Fin J → Fin L) (χ : Fin L → Fin L → ℂ),
    (∀ a b : Fin L,
      (1 / (L : ℂ)) * ∑ q : Fin L, χ a q * (χ b q)⁻¹ =
        if a = b then 1 else 0) →
      conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_cesaroMean phase χ =
        conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum phase

private lemma conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_collect
    {L J : ℕ} (phase : Fin J → Fin L) :
    (∑ i : Fin J, ∑ j : Fin J, if phase i = phase j then (1 : ℂ) else 0) =
      conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum phase := by
  classical
  have hinner : ∀ i j : Fin J,
      (∑ a : Fin L,
        (if phase i = a then (1 : ℂ) else 0) * (if phase j = a then (1 : ℂ) else 0)) =
        if phase i = phase j then (1 : ℂ) else 0 := by
    intro i j
    by_cases hij : phase i = phase j
    · simp [hij]
    · rw [Finset.sum_eq_zero]
      · simp [hij]
      · intro a _ha
        by_cases hi : phase i = a
        · have hj : ¬ phase j = a := by
            intro hja
            exact hij (hi.trans hja.symm)
          simp [hi, hj]
        · simp [hi]
  calc
    (∑ i : Fin J, ∑ j : Fin J, if phase i = phase j then (1 : ℂ) else 0) =
        ∑ i : Fin J, ∑ j : Fin J, ∑ a : Fin L,
          (if phase i = a then (1 : ℂ) else 0) *
            (if phase j = a then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [hinner i j]
    _ = ∑ a : Fin L, ∑ i : Fin J, ∑ j : Fin J,
          (if phase i = a then (1 : ℂ) else 0) *
            (if phase j = a then (1 : ℂ) else 0) := by
          calc
            (∑ i : Fin J, ∑ j : Fin J, ∑ a : Fin L,
                (if phase i = a then (1 : ℂ) else 0) *
                  (if phase j = a then (1 : ℂ) else 0)) =
                ∑ i : Fin J, ∑ a : Fin L, ∑ j : Fin J,
                  (if phase i = a then (1 : ℂ) else 0) *
                    (if phase j = a then (1 : ℂ) else 0) := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [Finset.sum_comm]
            _ = ∑ a : Fin L, ∑ i : Fin J, ∑ j : Fin J,
                  (if phase i = a then (1 : ℂ) else 0) *
                    (if phase j = a then (1 : ℂ) else 0) := by
                  rw [Finset.sum_comm]
    _ = ∑ a : Fin L,
          (∑ i : Fin J, if phase i = a then (1 : ℂ) else 0) *
            (∑ j : Fin J, if phase j = a then (1 : ℂ) else 0) := by
          apply Finset.sum_congr rfl
          intro a _ha
          symm
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _hi
          rw [Finset.mul_sum]
    _ = conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum phase := by
          simp [conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum,
            conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_multiplicity, pow_two]

/-- Paper label: `thm:conclusion-peripheral-phase-multiplicity-cesaro-quadratic-law`. -/
theorem paper_conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law :
    conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_statement := by
  classical
  intro L J _ phase χ hortho
  calc
    conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_cesaroMean phase χ =
        ∑ q : Fin L, ∑ i : Fin J, ∑ j : Fin J,
          (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹) := by
          rw [conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_cesaroMean,
            Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro q _hq
          calc
            (1 / (L : ℂ)) *
                ((∑ i : Fin J, χ (phase i) q) * (∑ j : Fin J, (χ (phase j) q)⁻¹)) =
                (1 / (L : ℂ)) *
                  (∑ i : Fin J, ∑ j : Fin J, χ (phase i) q * (χ (phase j) q)⁻¹) := by
                  congr 1
                  rw [Finset.sum_mul]
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [Finset.mul_sum]
            _ = ∑ i : Fin J, ∑ j : Fin J,
                  (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹) := by
                  rw [Finset.mul_sum]
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [Finset.mul_sum]
    _ = ∑ i : Fin J, ∑ j : Fin J, ∑ q : Fin L,
          (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹) := by
          calc
            (∑ q : Fin L, ∑ i : Fin J, ∑ j : Fin J,
                (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹)) =
                ∑ i : Fin J, ∑ q : Fin L, ∑ j : Fin J,
                  (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹) := by
                  rw [Finset.sum_comm]
            _ = ∑ i : Fin J, ∑ j : Fin J, ∑ q : Fin L,
                  (1 / (L : ℂ)) * (χ (phase i) q * (χ (phase j) q)⁻¹) := by
                  apply Finset.sum_congr rfl
                  intro i _hi
                  rw [Finset.sum_comm]
    _ = ∑ i : Fin J, ∑ j : Fin J,
          (1 / (L : ℂ)) * ∑ q : Fin L, χ (phase i) q * (χ (phase j) q)⁻¹ := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          rw [Finset.mul_sum]
    _ = ∑ i : Fin J, ∑ j : Fin J, if phase i = phase j then (1 : ℂ) else 0 := by
          apply Finset.sum_congr rfl
          intro i _hi
          apply Finset.sum_congr rfl
          intro j _hj
          exact hortho (phase i) (phase j)
    _ = conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_squareMultiplicitySum phase :=
          conclusion_peripheral_phase_multiplicity_cesaro_quadratic_law_collect phase

end

end Omega.Conclusion
