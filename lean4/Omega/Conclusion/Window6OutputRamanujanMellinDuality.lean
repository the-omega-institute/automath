import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

open scoped BigOperators

/-- The four conductor classes dividing `21`. -/
inductive conclusion_window6_output_ramanujan_mellin_duality_conductor
  | one
  | three
  | seven
  | twentyOne
  deriving DecidableEq, Fintype

open conclusion_window6_output_ramanujan_mellin_duality_conductor

/-- The three visible multiplicity layers of the `window-6` output. -/
def conclusion_window6_output_ramanujan_mellin_duality_layerSize : Fin 3 → ℝ
  | 0 => 2
  | 1 => 3
  | _ => 4

/-- Ramanujan layer charges aggregated from the residue set `R₆`. -/
def conclusion_window6_output_ramanujan_mellin_duality_layerCharge
    (q : conclusion_window6_output_ramanujan_mellin_duality_conductor) : Fin 3 → ℤ
  | 0 =>
      match q with
      | one => 8
      | three => -2
      | seven => -1
      | twentyOne => -5
  | 1 =>
      match q with
      | one => 4
      | three => 2
      | seven => -4
      | twentyOne => -2
  | _ =>
      match q with
      | one => 9
      | three => 0
      | seven => 5
      | twentyOne => 7

/-- Mellin-side Ramanujan profile for the three-layer `window-6` output. -/
noncomputable def conclusion_window6_output_ramanujan_mellin_duality_mellin
    (q : conclusion_window6_output_ramanujan_mellin_duality_conductor) (s : ℝ) : ℝ :=
  ∑ j : Fin 3,
    (conclusion_window6_output_ramanujan_mellin_duality_layerCharge q j : ℝ) *
      (conclusion_window6_output_ramanujan_mellin_duality_layerSize j) ^ s

/-- Capacity-side profile, written in the conductor-specific piecewise forms. -/
def conclusion_window6_output_ramanujan_mellin_duality_capacity
    (q : conclusion_window6_output_ramanujan_mellin_duality_conductor) (T : ℝ) : ℝ :=
  match q with
  | one =>
      if T ≤ 2 then
        21 * T
      else if T ≤ 3 then
        16 + 13 * T
      else if T ≤ 4 then
        28 + 9 * T
      else
        64
  | three =>
      if T ≤ 2 then
        0
      else if T ≤ 3 then
        2 * T - 4
      else
        2
  | seven =>
      if T ≤ 2 then
        0
      else if T ≤ 3 then
        T - 2
      else if T ≤ 4 then
        5 * T - 14
      else
        6
  | twentyOne =>
      if T ≤ 2 then
        0
      else if T ≤ 3 then
        5 * T - 10
      else if T ≤ 4 then
        7 * T - 16
      else
        12

/-- Finite Mellin-Barnes inverse written as the layerwise min-kernel superposition. -/
noncomputable def conclusion_window6_output_ramanujan_mellin_duality_inverse
    (q : conclusion_window6_output_ramanujan_mellin_duality_conductor) (T : ℝ) : ℝ :=
  ∑ j : Fin 3,
    (conclusion_window6_output_ramanujan_mellin_duality_layerCharge q j : ℝ) *
      min T (conclusion_window6_output_ramanujan_mellin_duality_layerSize j)

/-- Paper-facing `window-6` Ramanujan/Mellin duality package. -/
def conclusion_window6_output_ramanujan_mellin_duality_statement : Prop :=
  (∀ s : ℝ,
      conclusion_window6_output_ramanujan_mellin_duality_mellin one s =
        8 * (2 : ℝ) ^ s + 4 * (3 : ℝ) ^ s + 9 * (4 : ℝ) ^ s) ∧
    (∀ s : ℝ,
      conclusion_window6_output_ramanujan_mellin_duality_mellin three s =
        2 * (3 : ℝ) ^ s - 2 * (2 : ℝ) ^ s) ∧
    (∀ s : ℝ,
      conclusion_window6_output_ramanujan_mellin_duality_mellin seven s =
        5 * (4 : ℝ) ^ s - 4 * (3 : ℝ) ^ s - (2 : ℝ) ^ s) ∧
    (∀ s : ℝ,
      conclusion_window6_output_ramanujan_mellin_duality_mellin twentyOne s =
        7 * (4 : ℝ) ^ s - 2 * (3 : ℝ) ^ s - 5 * (2 : ℝ) ^ s) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity one T =
        conclusion_window6_output_ramanujan_mellin_duality_inverse one T) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity three T =
        conclusion_window6_output_ramanujan_mellin_duality_inverse three T) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity seven T =
        conclusion_window6_output_ramanujan_mellin_duality_inverse seven T) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity twentyOne T =
        conclusion_window6_output_ramanujan_mellin_duality_inverse twentyOne T)

private theorem conclusion_window6_output_ramanujan_mellin_duality_capacity_one_eq_inverse
    (T : ℝ) (_hT : 0 ≤ T) :
    conclusion_window6_output_ramanujan_mellin_duality_capacity one T =
      conclusion_window6_output_ramanujan_mellin_duality_inverse one T := by
  by_cases h2 : T ≤ 2
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_pos h2]
    rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
    have h3 : T ≤ 3 := le_trans h2 (by norm_num)
    have h4 : T ≤ 4 := le_trans h2 (by norm_num)
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_left h2,
      min_eq_left h3, min_eq_left h4]
    ring
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_neg h2]
    have h2' : 2 < T := lt_of_not_ge h2
    by_cases h3 : T ≤ 3
    · rw [if_pos h3]
      rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
      have h4 : T ≤ 4 := le_trans h3 (by norm_num)
      have h2le : 2 ≤ T := le_of_lt h2'
      simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
        conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
        min_eq_left h3, min_eq_left h4]
      ring
    · rw [if_neg h3]
      have h3' : 3 < T := lt_of_not_ge h3
      by_cases h4 : T ≤ 4
      · rw [if_pos h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_left h4]
        ring
      · rw [if_neg h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        have h4le : 4 ≤ T := le_of_not_ge h4
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_right h4le]
        ring

private theorem conclusion_window6_output_ramanujan_mellin_duality_capacity_three_eq_inverse
    (T : ℝ) (_hT : 0 ≤ T) :
    conclusion_window6_output_ramanujan_mellin_duality_capacity three T =
      conclusion_window6_output_ramanujan_mellin_duality_inverse three T := by
  by_cases h2 : T ≤ 2
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_pos h2]
    rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
    have h3 : T ≤ 3 := le_trans h2 (by norm_num)
    have h4 : T ≤ 4 := le_trans h2 (by norm_num)
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_left h2,
      min_eq_left h3, min_eq_left h4]
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_neg h2]
    have h2' : 2 < T := lt_of_not_ge h2
    by_cases h3 : T ≤ 3
    · rw [if_pos h3]
      rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
      have h4 : T ≤ 4 := le_trans h3 (by norm_num)
      have h2le : 2 ≤ T := le_of_lt h2'
      simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
        conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
        min_eq_left h3, min_eq_left h4]
      ring
    · rw [if_neg h3]
      rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
      have h2le : 2 ≤ T := by linarith
      have h3le : 3 ≤ T := le_of_not_ge h3
      simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
        conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
        min_eq_right h3le]
      norm_num

private theorem conclusion_window6_output_ramanujan_mellin_duality_capacity_seven_eq_inverse
    (T : ℝ) (_hT : 0 ≤ T) :
    conclusion_window6_output_ramanujan_mellin_duality_capacity seven T =
      conclusion_window6_output_ramanujan_mellin_duality_inverse seven T := by
  by_cases h2 : T ≤ 2
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_pos h2]
    rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
    have h3 : T ≤ 3 := le_trans h2 (by norm_num)
    have h4 : T ≤ 4 := le_trans h2 (by norm_num)
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_left h2,
      min_eq_left h3, min_eq_left h4]
    ring
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_neg h2]
    have h2' : 2 < T := lt_of_not_ge h2
    by_cases h3 : T ≤ 3
    · rw [if_pos h3]
      rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
      have h4 : T ≤ 4 := le_trans h3 (by norm_num)
      have h2le : 2 ≤ T := le_of_lt h2'
      simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
        conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
        min_eq_left h3, min_eq_left h4]
      ring
    · rw [if_neg h3]
      have h3' : 3 < T := lt_of_not_ge h3
      by_cases h4 : T ≤ 4
      · rw [if_pos h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_left h4]
        ring
      · rw [if_neg h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        have h4le : 4 ≤ T := le_of_not_ge h4
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_right h4le]
        ring

private theorem conclusion_window6_output_ramanujan_mellin_duality_capacity_twentyOne_eq_inverse
    (T : ℝ) (_hT : 0 ≤ T) :
    conclusion_window6_output_ramanujan_mellin_duality_capacity twentyOne T =
      conclusion_window6_output_ramanujan_mellin_duality_inverse twentyOne T := by
  by_cases h2 : T ≤ 2
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_pos h2]
    rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
    have h3 : T ≤ 3 := le_trans h2 (by norm_num)
    have h4 : T ≤ 4 := le_trans h2 (by norm_num)
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_left h2,
      min_eq_left h3, min_eq_left h4]
    ring
  · rw [conclusion_window6_output_ramanujan_mellin_duality_capacity, if_neg h2]
    have h2' : 2 < T := lt_of_not_ge h2
    by_cases h3 : T ≤ 3
    · rw [if_pos h3]
      rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
      have h4 : T ≤ 4 := le_trans h3 (by norm_num)
      have h2le : 2 ≤ T := le_of_lt h2'
      simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
        conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
        min_eq_left h3, min_eq_left h4]
      ring
    · rw [if_neg h3]
      have h3' : 3 < T := lt_of_not_ge h3
      by_cases h4 : T ≤ 4
      · rw [if_pos h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_left h4]
        ring
      · rw [if_neg h4]
        rw [conclusion_window6_output_ramanujan_mellin_duality_inverse, Fin.sum_univ_three]
        have h2le : 2 ≤ T := by linarith
        have h3le : 3 ≤ T := by linarith
        have h4le : 4 ≤ T := le_of_not_ge h4
        simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
          conclusion_window6_output_ramanujan_mellin_duality_layerSize, min_eq_right h2le,
          min_eq_right h3le, min_eq_right h4le]
        ring

/-- Paper label: `thm:conclusion-window6-output-ramanujan-mellin-duality`. The three visible
`window-6` multiplicity layers carry the same Ramanujan charges on both the Mellin side and the
capacity side; the Mellin profiles are the corresponding layerwise power sums, and the inverse
reconstructs the conductor capacity profile from the same finite min-kernel combination. -/
theorem paper_conclusion_window6_output_ramanujan_mellin_duality :
    conclusion_window6_output_ramanujan_mellin_duality_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro s
    rw [conclusion_window6_output_ramanujan_mellin_duality_mellin, Fin.sum_univ_three]
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize]
  · intro s
    rw [conclusion_window6_output_ramanujan_mellin_duality_mellin, Fin.sum_univ_three]
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize]
    ring
  · intro s
    rw [conclusion_window6_output_ramanujan_mellin_duality_mellin, Fin.sum_univ_three]
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize]
    ring
  · intro s
    rw [conclusion_window6_output_ramanujan_mellin_duality_mellin, Fin.sum_univ_three]
    simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge,
      conclusion_window6_output_ramanujan_mellin_duality_layerSize]
    ring
  · intro T hT
    exact conclusion_window6_output_ramanujan_mellin_duality_capacity_one_eq_inverse T hT
  · intro T hT
    exact conclusion_window6_output_ramanujan_mellin_duality_capacity_three_eq_inverse T hT
  · intro T hT
    exact conclusion_window6_output_ramanujan_mellin_duality_capacity_seven_eq_inverse T hT
  · intro T hT
    exact conclusion_window6_output_ramanujan_mellin_duality_capacity_twentyOne_eq_inverse T hT

/-- Paper label:
`thm:conclusion-window6-output-ramanujan-layer-charge-closedforms`. -/
theorem paper_conclusion_window6_output_ramanujan_layer_charge_closedforms :
    ((conclusion_window6_output_ramanujan_mellin_duality_layerCharge three 0,
      conclusion_window6_output_ramanujan_mellin_duality_layerCharge three 1,
      conclusion_window6_output_ramanujan_mellin_duality_layerCharge three 2) =
        ((-2 : ℤ), 2, 0)) ∧
      ((conclusion_window6_output_ramanujan_mellin_duality_layerCharge seven 0,
        conclusion_window6_output_ramanujan_mellin_duality_layerCharge seven 1,
        conclusion_window6_output_ramanujan_mellin_duality_layerCharge seven 2) =
          ((-1 : ℤ), -4, 5)) ∧
      ((conclusion_window6_output_ramanujan_mellin_duality_layerCharge twentyOne 0,
        conclusion_window6_output_ramanujan_mellin_duality_layerCharge twentyOne 1,
        conclusion_window6_output_ramanujan_mellin_duality_layerCharge twentyOne 2) =
          ((-5 : ℤ), -2, 7)) ∧
      conclusion_window6_output_ramanujan_mellin_duality_statement := by
  refine ⟨?_, ?_, ?_, paper_conclusion_window6_output_ramanujan_mellin_duality⟩
  · simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge]
  · simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge]
  · simp [conclusion_window6_output_ramanujan_mellin_duality_layerCharge]

/-- Paper label:
`thm:conclusion-window6-output-truncated-capacity-conductor-activation`. -/
theorem paper_conclusion_window6_output_truncated_capacity_conductor_activation :
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity three T =
        if T ≤ 2 then 0 else if T ≤ 3 then 2 * T - 4 else 2) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity seven T =
        if T ≤ 2 then 0 else if T ≤ 3 then T - 2 else if T ≤ 4 then 5 * T - 14 else 6) ∧
    (∀ T : ℝ, 0 ≤ T →
      conclusion_window6_output_ramanujan_mellin_duality_capacity twentyOne T =
        if T ≤ 2 then 0 else if T ≤ 3 then 5 * T - 10 else if T ≤ 4 then 7 * T - 16 else 12) := by
  refine ⟨?_, ?_, ?_⟩
  · intro T _hT
    rfl
  · intro T _hT
    rfl
  · intro T _hT
    rfl

end

end Omega.Conclusion
