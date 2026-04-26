import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Finset
open scoped BigOperators

/-- Finite product data for the conditional tensor average in a quadratic sign sector. -/
structure QuadraticSectorConditionalTensorAverageData where
  α : Type*
  β : Type*
  instFintypeα : Fintype α
  instDecEqα : DecidableEq α
  instFintypeβ : Fintype β
  instDecEqβ : DecidableEq β
  leftObservable : α → ℝ
  rightObservable : β → ℝ
  leftSign : α → ℝ
  rightSign : β → ℝ
  epsSign : ℝ
  deltaSign : ℝ
  cardα_pos : 0 < Fintype.card α
  cardβ_pos : 0 < Fintype.card β
  leftSignMean_zero :
    (∑ x : α, leftSign x) / Fintype.card α = 0
  rightSignMean_zero :
    (∑ y : β, rightSign y) / Fintype.card β = 0

attribute [instance] QuadraticSectorConditionalTensorAverageData.instFintypeα
attribute [instance] QuadraticSectorConditionalTensorAverageData.instDecEqα
attribute [instance] QuadraticSectorConditionalTensorAverageData.instFintypeβ
attribute [instance] QuadraticSectorConditionalTensorAverageData.instDecEqβ

namespace QuadraticSectorConditionalTensorAverageData

noncomputable def leftAverage (D : QuadraticSectorConditionalTensorAverageData) (f : D.α → ℝ) :
    ℝ :=
  (∑ x : D.α, f x) / Fintype.card D.α

noncomputable def rightAverage (D : QuadraticSectorConditionalTensorAverageData) (g : D.β → ℝ) :
    ℝ :=
  (∑ y : D.β, g y) / Fintype.card D.β

noncomputable def tensorAverage (D : QuadraticSectorConditionalTensorAverageData)
    (h : D.α → D.β → ℝ) : ℝ :=
  (∑ x : D.α, ∑ y : D.β, h x y) / (Fintype.card D.α * Fintype.card D.β)

noncomputable def eEps (D : QuadraticSectorConditionalTensorAverageData) (x : D.α) : ℝ :=
  (1 + D.epsSign * D.leftSign x) / 2

noncomputable def eDelta (D : QuadraticSectorConditionalTensorAverageData) (y : D.β) : ℝ :=
  (1 + D.deltaSign * D.rightSign y) / 2

noncomputable def sectorIndicator (D : QuadraticSectorConditionalTensorAverageData)
    (x : D.α) (y : D.β) : ℝ :=
  D.eEps x * D.eDelta y

noncomputable def sectorDensity (D : QuadraticSectorConditionalTensorAverageData) : ℝ :=
  D.tensorAverage D.sectorIndicator

noncomputable def sectorConditionalAverage (D : QuadraticSectorConditionalTensorAverageData) :
    ℝ :=
  D.tensorAverage
      (fun x y => D.sectorIndicator x y * D.leftObservable x * D.rightObservable y) /
    D.sectorDensity

noncomputable def leftSignedAverage (D : QuadraticSectorConditionalTensorAverageData) : ℝ :=
  D.leftAverage (fun x => D.leftSign x * D.leftObservable x)

noncomputable def rightSignedAverage (D : QuadraticSectorConditionalTensorAverageData) : ℝ :=
  D.rightAverage (fun y => D.rightSign y * D.rightObservable y)

def sectorAverageFormula (D : QuadraticSectorConditionalTensorAverageData) : Prop :=
  D.sectorConditionalAverage =
    (D.leftAverage D.leftObservable + D.epsSign * D.leftSignedAverage) *
      (D.rightAverage D.rightObservable + D.deltaSign * D.rightSignedAverage)

end QuadraticSectorConditionalTensorAverageData

private lemma tensorAverage_mul (D : QuadraticSectorConditionalTensorAverageData)
    (f : D.α → ℝ) (g : D.β → ℝ) :
    D.tensorAverage (fun x y => f x * g y) = D.leftAverage f * D.rightAverage g := by
  unfold QuadraticSectorConditionalTensorAverageData.tensorAverage
    QuadraticSectorConditionalTensorAverageData.leftAverage
    QuadraticSectorConditionalTensorAverageData.rightAverage
  have hsum :
      (∑ x : D.α, ∑ y : D.β, f x * g y) = (∑ x : D.α, f x) * ∑ y : D.β, g y := by
    calc
      (∑ x : D.α, ∑ y : D.β, f x * g y) = ∑ x : D.α, f x * ∑ y : D.β, g y := by
        refine Finset.sum_congr rfl ?_
        intro x hx
        rw [Finset.mul_sum]
      _ = (∑ x : D.α, f x) * ∑ y : D.β, g y := by
        rw [Finset.sum_mul]
  rw [hsum]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardα_pos),
    Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardβ_pos)]

private lemma leftAverage_projector (D : QuadraticSectorConditionalTensorAverageData)
    (f : D.α → ℝ) :
    D.leftAverage (fun x => D.eEps x * f x) =
      (D.leftAverage f + D.epsSign * D.leftAverage (fun x => D.leftSign x * f x)) / 2 := by
  unfold QuadraticSectorConditionalTensorAverageData.leftAverage
    QuadraticSectorConditionalTensorAverageData.eEps
  have hsum :
      ∑ x : D.α, ((1 + D.epsSign * D.leftSign x) / 2) * f x =
        ((∑ x : D.α, f x) + D.epsSign * ∑ x : D.α, D.leftSign x * f x) / 2 := by
    calc
      ∑ x : D.α, ((1 + D.epsSign * D.leftSign x) / 2) * f x
          = ∑ x : D.α, (f x + D.epsSign * (D.leftSign x * f x)) / 2 := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              ring
      _ = ((∑ x : D.α, f x) + ∑ x : D.α, D.epsSign * (D.leftSign x * f x)) / 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ = ((∑ x : D.α, f x) + D.epsSign * ∑ x : D.α, D.leftSign x * f x) / 2 := by
            rw [← Finset.mul_sum]
  rw [hsum]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardα_pos)]

private lemma rightAverage_projector (D : QuadraticSectorConditionalTensorAverageData)
    (g : D.β → ℝ) :
    D.rightAverage (fun y => D.eDelta y * g y) =
      (D.rightAverage g + D.deltaSign * D.rightAverage (fun y => D.rightSign y * g y)) / 2 := by
  unfold QuadraticSectorConditionalTensorAverageData.rightAverage
    QuadraticSectorConditionalTensorAverageData.eDelta
  have hsum :
      ∑ y : D.β, ((1 + D.deltaSign * D.rightSign y) / 2) * g y =
        ((∑ y : D.β, g y) + D.deltaSign * ∑ y : D.β, D.rightSign y * g y) / 2 := by
    calc
      ∑ y : D.β, ((1 + D.deltaSign * D.rightSign y) / 2) * g y
          = ∑ y : D.β, (g y + D.deltaSign * (D.rightSign y * g y)) / 2 := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              ring
      _ = ((∑ y : D.β, g y) + ∑ y : D.β, D.deltaSign * (D.rightSign y * g y)) / 2 := by
            rw [← Finset.sum_div, Finset.sum_add_distrib]
      _ = ((∑ y : D.β, g y) + D.deltaSign * ∑ y : D.β, D.rightSign y * g y) / 2 := by
            rw [← Finset.mul_sum]
  rw [hsum]
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardβ_pos)]

private lemma sectorDensity_eq_quarter (D : QuadraticSectorConditionalTensorAverageData) :
    D.sectorDensity = 1 / 4 := by
  unfold QuadraticSectorConditionalTensorAverageData.sectorDensity
  change D.tensorAverage (fun x y => D.eEps x * D.eDelta y) = 1 / 4
  rw [tensorAverage_mul]
  have honeLeft : D.leftAverage (fun _ => (1 : ℝ)) = 1 := by
    unfold QuadraticSectorConditionalTensorAverageData.leftAverage
    simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardα_pos)]
  have honeRight : D.rightAverage (fun _ => (1 : ℝ)) = 1 := by
    unfold QuadraticSectorConditionalTensorAverageData.rightAverage
    simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.cardβ_pos)]
  have hleft :
      D.leftAverage (fun x => D.eEps x) = 1 / 2 := by
    have hsign :
        D.leftAverage (fun x => D.leftSign x * 1) = 0 := by
      simpa [QuadraticSectorConditionalTensorAverageData.leftAverage] using D.leftSignMean_zero
    have hsign0 : D.leftAverage D.leftSign = 0 := by
      simpa using hsign
    calc
      D.leftAverage (fun x => D.eEps x) =
          (D.leftAverage (fun _ => (1 : ℝ)) +
            D.epsSign * D.leftAverage (fun x => D.leftSign x * 1)) / 2 := by
              simpa using (leftAverage_projector D (fun _ => (1 : ℝ)))
      _ = 1 / 2 := by simp [honeLeft, hsign0]
  have hright :
      D.rightAverage (fun y => D.eDelta y) = 1 / 2 := by
    have hsign :
        D.rightAverage (fun y => D.rightSign y * 1) = 0 := by
      simpa [QuadraticSectorConditionalTensorAverageData.rightAverage] using D.rightSignMean_zero
    have hsign0 : D.rightAverage D.rightSign = 0 := by
      simpa using hsign
    calc
      D.rightAverage (fun y => D.eDelta y) =
          (D.rightAverage (fun _ => (1 : ℝ)) +
            D.deltaSign * D.rightAverage (fun y => D.rightSign y * 1)) / 2 := by
              simpa using (rightAverage_projector D (fun _ => (1 : ℝ)))
      _ = 1 / 2 := by simp [honeRight, hsign0]
  rw [hleft, hright]
  norm_num

/-- In the balanced quadratic sign sector, the conditional average of a tensor observable is the
affine sign-corrected product of the one-variable averages.
    thm:xi-time-part9zg-quadratic-sector-conditional-tensor-average -/
theorem paper_xi_time_part9zg_quadratic_sector_conditional_tensor_average
    (D : QuadraticSectorConditionalTensorAverageData) :
    D.sectorAverageFormula := by
  have hnum :
      D.tensorAverage
          (fun x y => D.eEps x * D.eDelta y * D.leftObservable x * D.rightObservable y) =
        D.tensorAverage
          (fun x y => (D.eEps x * D.leftObservable x) * (D.eDelta y * D.rightObservable y)) := by
    refine congrArg D.tensorAverage ?_
    funext x y
    ring
  unfold QuadraticSectorConditionalTensorAverageData.sectorAverageFormula
    QuadraticSectorConditionalTensorAverageData.sectorConditionalAverage
    QuadraticSectorConditionalTensorAverageData.leftSignedAverage
    QuadraticSectorConditionalTensorAverageData.rightSignedAverage
    QuadraticSectorConditionalTensorAverageData.sectorIndicator
  rw [hnum]
  rw [tensorAverage_mul]
  rw [leftAverage_projector, rightAverage_projector, sectorDensity_eq_quarter]
  field_simp
  ring

/-- Concrete block data for the splitting-density refinement: the observables are indicator
functions of two finite blocks on which the sign characters are constant. -/
structure xi_time_part9zg_quadratic_sector_conditional_splitting_density_data where
  base : QuadraticSectorConditionalTensorAverageData
  leftBlock : Finset base.α
  rightBlock : Finset base.β
  leftBlockSign : ℝ
  rightBlockSign : ℝ
  leftBlock_sign :
    ∀ x : base.α, x ∈ leftBlock → base.leftSign x = leftBlockSign
  rightBlock_sign :
    ∀ y : base.β, y ∈ rightBlock → base.rightSign y = rightBlockSign
  leftBlockSign_sq : leftBlockSign ^ 2 = 1
  rightBlockSign_sq : rightBlockSign ^ 2 = 1
  epsSign_sq : base.epsSign ^ 2 = 1
  deltaSign_sq : base.deltaSign ^ 2 = 1

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data)
    (x : D.base.α) : ℝ :=
  if x ∈ D.leftBlock then 1 else 0

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data)
    (y : D.base.β) : ℝ :=
  if y ∈ D.rightBlock then 1 else 0

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) :
    QuadraticSectorConditionalTensorAverageData where
  α := D.base.α
  β := D.base.β
  instFintypeα := D.base.instFintypeα
  instDecEqα := D.base.instDecEqα
  instFintypeβ := D.base.instFintypeβ
  instDecEqβ := D.base.instDecEqβ
  leftObservable := xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D
  rightObservable := xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D
  leftSign := D.base.leftSign
  rightSign := D.base.rightSign
  epsSign := D.base.epsSign
  deltaSign := D.base.deltaSign
  cardα_pos := D.base.cardα_pos
  cardβ_pos := D.base.cardβ_pos
  leftSignMean_zero := D.base.leftSignMean_zero
  rightSignMean_zero := D.base.rightSignMean_zero

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) : ℝ :=
  D.base.leftAverage
    (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D)

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) : ℝ :=
  D.base.rightAverage
    (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D)

noncomputable def xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) : ℝ :=
  (xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data D).sectorConditionalAverage

def xi_time_part9zg_quadratic_sector_conditional_splitting_density_spec
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) : Prop :=
  xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
    if D.base.epsSign = D.leftBlockSign ∧ D.base.deltaSign = D.rightBlockSign then
      4 * xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D *
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D
    else 0

private lemma xi_time_part9zg_quadratic_sector_conditional_splitting_density_eq_one_or_neg_one
    {a : ℝ} (ha : a ^ 2 = 1) : a = 1 ∨ a = -1 := by
  have hprod : (a - 1) * (a + 1) = 0 := by
    nlinarith [ha]
  rcases mul_eq_zero.mp hprod with hleft | hright
  · left
    linarith
  · right
    linarith

private lemma xi_time_part9zg_quadratic_sector_conditional_splitting_density_sign_factor
    {a b : ℝ} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) :
    1 + a * b = if a = b then 2 else 0 := by
  rcases
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_eq_one_or_neg_one ha with
    ha' | ha' <;>
    rcases
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_eq_one_or_neg_one hb with
    hb' | hb' <;>
    norm_num [ha', hb']

private lemma xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_signed_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) :
    D.base.leftAverage
        (fun x =>
          D.base.leftSign x *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D x) =
      D.leftBlockSign *
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D := by
  unfold QuadraticSectorConditionalTensorAverageData.leftAverage
    xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density
    xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator
  have hsum :
      ∑ x : D.base.α, D.base.leftSign x * (if x ∈ D.leftBlock then 1 else 0) =
        D.leftBlockSign * ∑ x : D.base.α, (if x ∈ D.leftBlock then 1 else 0) := by
    calc
      ∑ x : D.base.α, D.base.leftSign x * (if x ∈ D.leftBlock then 1 else 0)
          = ∑ x : D.base.α, D.leftBlockSign * (if x ∈ D.leftBlock then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              by_cases hmem : x ∈ D.leftBlock
              · simp [hmem, D.leftBlock_sign x hmem]
              · simp [hmem]
      _ = D.leftBlockSign * ∑ x : D.base.α, (if x ∈ D.leftBlock then 1 else 0) := by
            rw [Finset.mul_sum]
  rw [hsum]
  calc
    (D.leftBlockSign * ∑ x : D.base.α, if x ∈ D.leftBlock then 1 else 0) /
        Fintype.card D.base.α =
      D.leftBlockSign *
        ((∑ x : D.base.α, if x ∈ D.leftBlock then 1 else 0) / Fintype.card D.base.α) := by
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.base.cardα_pos)]
    _ = D.leftBlockSign *
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D := by
          rfl

private lemma xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_signed_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) :
    D.base.rightAverage
        (fun y =>
          D.base.rightSign y *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D y) =
      D.rightBlockSign *
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D := by
  unfold QuadraticSectorConditionalTensorAverageData.rightAverage
    xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density
    xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator
  have hsum :
      ∑ y : D.base.β, D.base.rightSign y * (if y ∈ D.rightBlock then 1 else 0) =
        D.rightBlockSign * ∑ y : D.base.β, (if y ∈ D.rightBlock then 1 else 0) := by
    calc
      ∑ y : D.base.β, D.base.rightSign y * (if y ∈ D.rightBlock then 1 else 0)
          = ∑ y : D.base.β, D.rightBlockSign * (if y ∈ D.rightBlock then 1 else 0) := by
              refine Finset.sum_congr rfl ?_
              intro y hy
              by_cases hmem : y ∈ D.rightBlock
              · simp [hmem, D.rightBlock_sign y hmem]
              · simp [hmem]
      _ = D.rightBlockSign * ∑ y : D.base.β, (if y ∈ D.rightBlock then 1 else 0) := by
            rw [Finset.mul_sum]
  rw [hsum]
  calc
    (D.rightBlockSign * ∑ y : D.base.β, if y ∈ D.rightBlock then 1 else 0) /
        Fintype.card D.base.β =
      D.rightBlockSign *
        ((∑ y : D.base.β, if y ∈ D.rightBlock then 1 else 0) / Fintype.card D.base.β) := by
          field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt D.base.cardβ_pos)]
    _ = D.rightBlockSign *
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D := by
          rfl

/-- Indicator functions of conjugacy-class blocks reduce the conditional tensor-average formula to
the sign-matching splitting-density table: mismatched signs give zero, while matched signs give a
uniform factor `4` times the base product density.
    thm:xi-time-part9zg-quadratic-sector-conditional-splitting-density -/
theorem paper_xi_time_part9zg_quadratic_sector_conditional_splitting_density
    (D : xi_time_part9zg_quadratic_sector_conditional_splitting_density_data) :
    xi_time_part9zg_quadratic_sector_conditional_splitting_density_spec D := by
  let T := xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data D
  have hT : T.sectorAverageFormula := by
    exact paper_xi_time_part9zg_quadratic_sector_conditional_tensor_average T
  have hformula₀ :
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
        (T.leftAverage
            (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D) +
            D.base.epsSign *
              T.leftAverage
                (fun x =>
                  D.base.leftSign x *
                    xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator
                      D x)) *
          (T.rightAverage
            (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D) +
            D.base.deltaSign *
              T.rightAverage
                (fun y =>
                  D.base.rightSign y *
                    xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator
                      D y)) := by
    simpa [T,
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data,
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density,
      QuadraticSectorConditionalTensorAverageData.sectorAverageFormula,
      QuadraticSectorConditionalTensorAverageData.leftSignedAverage,
      QuadraticSectorConditionalTensorAverageData.rightSignedAverage] using hT
  have hformula :
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
        (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D +
            D.base.epsSign * (D.leftBlockSign *
              xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D)) *
          (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D +
            D.base.deltaSign * (D.rightBlockSign *
              xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D)) := by
    have hleft_avg :
        T.leftAverage
            (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D) =
          xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D := by
      rfl
    have hright_avg :
        T.rightAverage
            (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D) =
          xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D := by
      rfl
    have hleft_signed :
        T.leftAverage
            (fun x =>
              D.base.leftSign x *
                xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D x) =
          D.leftBlockSign *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D := by
      simpa [T, xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data] using
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_signed_density D
    have hright_signed :
        T.rightAverage
            (fun y =>
              D.base.rightSign y *
                xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D y) =
          D.rightBlockSign *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D := by
      simpa [T, xi_time_part9zg_quadratic_sector_conditional_splitting_density_tensor_data] using
        xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_signed_density D
    calc
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
          (T.leftAverage
              (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator D) +
              D.base.epsSign *
                T.leftAverage
                  (fun x =>
                    D.base.leftSign x *
                      xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_indicator
                        D x)) *
            (T.rightAverage
              (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator D) +
              D.base.deltaSign *
                T.rightAverage
                  (fun y =>
                    D.base.rightSign y *
                      xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_indicator
                        D y)) := hformula₀
      _ = (xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D +
              D.base.epsSign * (D.leftBlockSign *
                xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D)) *
            (xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D +
              D.base.deltaSign * (D.rightBlockSign *
                xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D)) := by
            rw [hleft_avg, hleft_signed, hright_avg, hright_signed]
  have hleft_factor :
      1 + D.base.epsSign * D.leftBlockSign =
        if D.base.epsSign = D.leftBlockSign then 2 else 0 := by
    exact
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_sign_factor
        D.epsSign_sq D.leftBlockSign_sq
  have hright_factor :
      1 + D.base.deltaSign * D.rightBlockSign =
        if D.base.deltaSign = D.rightBlockSign then 2 else 0 := by
    exact
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_sign_factor
        D.deltaSign_sq D.rightBlockSign_sq
  have hfactorized :
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
        ((if D.base.epsSign = D.leftBlockSign then 2 else 0) *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D) *
          ((if D.base.deltaSign = D.rightBlockSign then 2 else 0) *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D) := by
    calc
      xi_time_part9zg_quadratic_sector_conditional_splitting_density_conditional_density D =
          ((1 + D.base.epsSign * D.leftBlockSign) *
              xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D) *
            ((1 + D.base.deltaSign * D.rightBlockSign) *
              xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D) := by
            rw [hformula]
            ring
      _ = ((if D.base.epsSign = D.leftBlockSign then 2 else 0) *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_left_density D) *
          ((if D.base.deltaSign = D.rightBlockSign then 2 else 0) *
            xi_time_part9zg_quadratic_sector_conditional_splitting_density_right_density D) := by
            rw [hleft_factor, hright_factor]

  unfold xi_time_part9zg_quadratic_sector_conditional_splitting_density_spec
  by_cases hε : D.base.epsSign = D.leftBlockSign
  · by_cases hδ : D.base.deltaSign = D.rightBlockSign
    · simp [hfactorized, hε, hδ]
      ring
    · simp [hfactorized, hε, hδ]
  · by_cases hδ : D.base.deltaSign = D.rightBlockSign
    · simp [hfactorized, hε, hδ]
    · simp [hfactorized, hε, hδ]

end Omega.Zeta
