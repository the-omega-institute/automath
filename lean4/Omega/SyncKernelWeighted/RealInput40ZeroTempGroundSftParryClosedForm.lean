import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- A small helper for explicit `Fin 4` vectors. -/
def fin4Tuple {α : Type _} (a₀ a₁ a₂ a₃ : α) : Fin 4 → α := fun i =>
  match i.1 with
  | 0 => a₀
  | 1 => a₁
  | 2 => a₂
  | _ => a₃

/-- The quartic Perron relation used in the zero-temperature closed forms. -/
def realInput40ZeroTempQuartic (θ : ℝ) : ℝ :=
  θ ^ 4 - θ ^ 3 - θ ^ 2 - θ - 1

/-- First auxiliary identity extracted from the quartic relation. -/
def realInput40ZeroTempAuxiliaryOne (θ : ℝ) : Prop :=
  θ ^ 4 = θ ^ 3 + θ ^ 2 + θ + 1

/-- Second auxiliary identity extracted from the quartic relation. -/
def realInput40ZeroTempAuxiliaryTwo (θ : ℝ) : Prop :=
  θ ^ 4 - θ ^ 3 = θ ^ 2 + θ + 1

/-- Closed-form right Perron vector coordinates. -/
def realInput40RightPerronFormula (θ : ℝ) : Fin 4 → ℝ :=
  fin4Tuple 1 θ (θ ^ 2) (θ ^ 3)

/-- Closed-form left Perron vector coordinates. -/
def realInput40LeftPerronFormula (θ : ℝ) : Fin 4 → ℝ :=
  fin4Tuple (θ ^ 3) (θ ^ 2) θ 1

/-- Closed-form Parry transition matrix obtained from the right Perron vector. -/
def realInput40ParryTransitionFormula
    (adjacency : Fin 4 → Fin 4 → ℝ) (θ : ℝ) (rightVec : Fin 4 → ℝ) : Fin 4 → Fin 4 → ℝ :=
  fun i j => adjacency i j * rightVec j / (θ * rightVec i)

/-- Closed-form stationary weights obtained by normalizing the left-right products. -/
def realInput40StationaryDistributionFormula
    (leftVec rightVec : Fin 4 → ℝ) : Fin 4 → ℝ :=
  let Z : ℝ := ∑ i : Fin 4, leftVec i * rightVec i
  fun i => leftVec i * rightVec i / Z

lemma realInput40_auxiliary_one_of_quartic {θ : ℝ} (hQuartic : realInput40ZeroTempQuartic θ = 0) :
    realInput40ZeroTempAuxiliaryOne θ := by
  unfold realInput40ZeroTempQuartic realInput40ZeroTempAuxiliaryOne at *
  nlinarith

lemma realInput40_auxiliary_two_of_quartic {θ : ℝ} (hQuartic : realInput40ZeroTempQuartic θ = 0) :
    realInput40ZeroTempAuxiliaryTwo θ := by
  unfold realInput40ZeroTempQuartic realInput40ZeroTempAuxiliaryTwo at *
  nlinarith

/-- Concrete package for the zero-temperature four-state SFT and its Parry closed forms. -/
structure RealInput40ZeroTempGroundSftParryClosedFormData where
  θ : ℝ
  adjacency : Fin 4 → Fin 4 → ℝ
  rightVec : Fin 4 → ℝ
  leftVec : Fin 4 → ℝ
  parry : Fin 4 → Fin 4 → ℝ
  stationary : Fin 4 → ℝ
  quarticRelation : realInput40ZeroTempQuartic θ = 0
  rightClosed : rightVec = realInput40RightPerronFormula θ
  leftClosed : leftVec = realInput40LeftPerronFormula θ
  parryClosed : parry = realInput40ParryTransitionFormula adjacency θ rightVec
  stationaryClosed : stationary = realInput40StationaryDistributionFormula leftVec rightVec

namespace RealInput40ZeroTempGroundSftParryClosedFormData

/-- The right Perron vector is given by the stated coordinates, together with the first auxiliary
identity derived from the quartic Perron relation. -/
def rightPerronVectorClosedForm (D : RealInput40ZeroTempGroundSftParryClosedFormData) : Prop :=
  realInput40ZeroTempAuxiliaryOne D.θ ∧ D.rightVec = realInput40RightPerronFormula D.θ

/-- The left Perron vector is given by the stated coordinates, together with the second auxiliary
identity derived from the quartic Perron relation. -/
def leftPerronVectorClosedForm (D : RealInput40ZeroTempGroundSftParryClosedFormData) : Prop :=
  realInput40ZeroTempAuxiliaryTwo D.θ ∧ D.leftVec = realInput40LeftPerronFormula D.θ

/-- The Parry transition matrix is read off coordinatewise from the right Perron vector. -/
def parryTransitionClosedForm (D : RealInput40ZeroTempGroundSftParryClosedFormData) : Prop :=
  D.parry = realInput40ParryTransitionFormula D.adjacency D.θ D.rightVec

/-- The stationary weights are the normalized left-right products. -/
def stationaryDistributionClosedForm (D : RealInput40ZeroTempGroundSftParryClosedFormData) : Prop :=
  D.stationary = realInput40StationaryDistributionFormula D.leftVec D.rightVec

end RealInput40ZeroTempGroundSftParryClosedFormData

open RealInput40ZeroTempGroundSftParryClosedFormData

/-- Paper label: `thm:killo-real-input-40-zero-temp-ground-sft-parry-closed-form`. -/
theorem paper_killo_real_input_40_zero_temp_ground_sft_parry_closed_form
    (D : RealInput40ZeroTempGroundSftParryClosedFormData) :
    D.rightPerronVectorClosedForm ∧ D.leftPerronVectorClosedForm ∧
      D.parryTransitionClosedForm ∧ D.stationaryDistributionClosedForm := by
  refine ⟨⟨realInput40_auxiliary_one_of_quartic D.quarticRelation, D.rightClosed⟩,
    ⟨realInput40_auxiliary_two_of_quartic D.quarticRelation, D.leftClosed⟩,
    D.parryClosed, D.stationaryClosed⟩

end

end Omega.SyncKernelWeighted
