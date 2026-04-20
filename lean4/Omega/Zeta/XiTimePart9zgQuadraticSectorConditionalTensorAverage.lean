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

end Omega.Zeta
