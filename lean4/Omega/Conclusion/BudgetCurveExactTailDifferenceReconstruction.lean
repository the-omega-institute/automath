import Mathlib.Tactic
import Omega.Conclusion.CapacityRamanujanPlateauLaw

namespace Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

private theorem card_eq_card_ge_sub_card_ge_succ (d : α → ℕ) (k : ℕ) :
    (Finset.univ.filter (fun x => d x = k)).card =
      (Finset.univ.filter fun x => k ≤ d x).card -
        (Finset.univ.filter fun x => k + 1 ≤ d x).card := by
  classical
  let A : Finset α := Finset.univ.filter fun x => k ≤ d x
  let B : Finset α := Finset.univ.filter fun x => k + 1 ≤ d x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = Finset.univ.filter (fun x => d x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (Finset.univ.filter (fun x => d x = k)).card = A.card - B.card := by
    rw [← hsplit, Finset.card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

omit [DecidableEq α] in
private theorem deltaCapacity_eq_count_ge (d : α → ℕ) (s : ℕ) (hs : 1 ≤ s) :
    Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s = #{x | s ≤ d x} := by
  rw [Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity_eq_card_ge d s hs]
  exact Fintype.card_of_subtype (Finset.univ.filter fun x => s ≤ d x) (by
    intro x
    simp)

/-- Paper seed: the discrete budget curve jump is the tail count, and tail differences recover
    the exact multiplicity histogram.
    thm:conclusion-budget-curve-exact-tail-difference-reconstruction -/
theorem paper_conclusion_budget_curve_exact_tail_difference_reconstruction_seeds
    (d : α → ℕ) (s k : ℕ) (hs : 1 ≤ s) (hk : 1 ≤ k) :
    Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d s =
      #{x | s ≤ d x} ∧
      #{x | d x = k} =
        Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d k -
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d (k + 1) ∧
      (∀ d' : α → ℕ,
        (∀ t : ℕ,
          Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d t =
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' t) →
        #{x | d x = k} = #{x | d' x = k}) := by
  refine ⟨deltaCapacity_eq_count_ge d s hs, ?_, ?_⟩
  · rw [deltaCapacity_eq_count_ge d k hk,
      deltaCapacity_eq_count_ge d (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
    simpa [Nat.succ_le_iff] using card_eq_card_ge_sub_card_ge_succ (α := α) d k
  · intro d' hdelta
    calc
      #{x | d x = k}
          = Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d k -
              Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d (k + 1) := by
              rw [deltaCapacity_eq_count_ge d k hk,
                deltaCapacity_eq_count_ge d (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
              simpa [Nat.succ_le_iff] using card_eq_card_ge_sub_card_ge_succ (α := α) d k
      _ = Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' k -
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' (k + 1) := by
            rw [hdelta k, hdelta (k + 1)]
      _ = #{x | d' x = k} := by
            rw [deltaCapacity_eq_count_ge d' k hk,
              deltaCapacity_eq_count_ge d' (k + 1) (Nat.succ_le_succ (Nat.zero_le k))]
            simpa [Nat.succ_le_iff] using (card_eq_card_ge_sub_card_ge_succ (α := α) d' k).symm

/-- Any observable that depends only on the multiplicity histogram factors through the exact budget
curve. This is the paper-facing Mellin--Rényi factorization layer wrapper. -/
theorem paper_conclusion_budget_curve_mellin_renyi_factorization_layer
    {β : Type*} (Obs : (α → ℕ) → β)
    (hObs : ∀ d d', (∀ k : ℕ, #{x | d x = k} = #{x | d' x = k}) → Obs d = Obs d')
    (d d' : α → ℕ)
    (hcurve : ∀ t : ℕ,
      Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d t =
        Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' t) :
    Obs d = Obs d' := by
  apply hObs
  intro k
  by_cases hk : k = 0
  · subst hk
    calc
      #{x | d x = 0} = Fintype.card α - #{x | 1 ≤ d x} := by
        simpa using (card_eq_card_ge_sub_card_ge_succ (α := α) d 0)
      _ = Fintype.card α -
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d 1 := by
          rw [deltaCapacity_eq_count_ge d 1 (by norm_num)]
      _ = Fintype.card α -
            Omega.Conclusion.CapacityRamanujanPlateauLaw.deltaCapacity d' 1 := by
          rw [hcurve 1]
      _ = Fintype.card α - #{x | 1 ≤ d' x} := by
          rw [deltaCapacity_eq_count_ge d' 1 (by norm_num)]
      _ = #{x | d' x = 0} := by
          symm
          simpa using (card_eq_card_ge_sub_card_ge_succ (α := α) d' 0)
  · have hk1 : 1 ≤ k := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hk)
    exact
      (paper_conclusion_budget_curve_exact_tail_difference_reconstruction_seeds
        (α := α) d k k hk1 hk1).2.2 d' hcurve

theorem paper_conclusion_capacity_exponent_universal_fold_angle
    (gStar alphaStar beta : ℝ) :
    let betaC := alphaStar / Real.log 2
    let lowerGamma := gStar + min alphaStar (beta * Real.log 2)
    (beta ≤ betaC → lowerGamma = gStar + beta * Real.log 2) ∧
      (betaC ≤ beta → lowerGamma = gStar + alphaStar) := by
  dsimp
  have hlog2 : 0 < Real.log 2 := by
    exact Real.log_pos (by norm_num : (1 : ℝ) < 2)
  constructor
  · intro hbeta
    have hmin : beta * Real.log 2 ≤ alphaStar := by
      have hmul := mul_le_mul_of_nonneg_right hbeta hlog2.le
      simpa [div_eq_mul_inv, hlog2.ne'] using hmul
    rw [min_eq_right hmin]
  · intro hbeta
    have hmin : alphaStar ≤ beta * Real.log 2 := by
      have hmul := mul_le_mul_of_nonneg_right hbeta hlog2.le
      simpa [div_eq_mul_inv, hlog2.ne'] using hmul
    rw [min_eq_left hmin]

end Omega.Conclusion.BudgetCurveExactTailDifferenceReconstruction
