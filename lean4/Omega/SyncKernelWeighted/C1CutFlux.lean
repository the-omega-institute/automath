import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open scoped BigOperators

noncomputable section

/-- Concrete data for the `κ = 1` cut-flux identity. The left/right Perron vectors are represented
by finitely supported functions, and the `core → core` block of `A₁` vanishes. -/
structure C1CutFluxData where
  ι : Type
  instFintype : Fintype ι
  instDecidableEq : DecidableEq ι
  A0 : ι → ι → ℝ
  A1 : ι → ι → ℝ
  leftVec : ι → ℝ
  rightVec : ι → ℝ
  leftSupport : Finset ι
  rightSupport : Finset ι
  core : Finset ι
  left_zero_outside : ∀ i, i ∉ leftSupport → leftVec i = 0
  right_zero_outside : ∀ j, j ∉ rightSupport → rightVec j = 0
  zero_core_block : ∀ i, i ∈ core → ∀ j, j ∈ core → A1 i j = 0

attribute [instance] C1CutFluxData.instFintype C1CutFluxData.instDecidableEq

namespace C1CutFluxData

/-- The full bilinear first-order response `lᵀ A₁ r`. -/
def firstOrderResponse (D : C1CutFluxData) : ℝ :=
  ∑ i : D.ι, ∑ j : D.ι, D.leftVec i * D.A1 i j * D.rightVec j

/-- The same bilinear form, restricted to the supports of the left and right Perron vectors. -/
def supportedResponse (D : C1CutFluxData) : ℝ :=
  ∑ i : D.ι, ∑ j : D.ι,
    if i ∈ D.leftSupport ∧ j ∈ D.rightSupport then
      D.leftVec i * D.A1 i j * D.rightVec j
    else 0

/-- The weighted cut-flux: support-restricted contributions with the `core → core` block removed. -/
def cutFlux (D : C1CutFluxData) : ℝ :=
  ∑ i : D.ι, ∑ j : D.ι,
    if i ∈ D.leftSupport ∧ j ∈ D.rightSupport ∧ ¬ (i ∈ D.core ∧ j ∈ D.core) then
      D.leftVec i * D.A1 i j * D.rightVec j
    else 0

/-- Expanding `lᵀ A₁ r` as a double sum and discarding indices outside the supports. -/
def firstOrderResponseLaw (D : C1CutFluxData) : Prop :=
  D.firstOrderResponse = D.supportedResponse

/-- After removing the zero `core → core` block, the surviving terms are exactly the weighted
cut-flux contributions. -/
def cutFluxRestriction (D : C1CutFluxData) : Prop :=
  D.supportedResponse = D.cutFlux

lemma firstOrder_term_eq_supported (D : C1CutFluxData) (i j : D.ι) :
    D.leftVec i * D.A1 i j * D.rightVec j =
      if i ∈ D.leftSupport ∧ j ∈ D.rightSupport then
        D.leftVec i * D.A1 i j * D.rightVec j
      else 0 := by
  by_cases hi : i ∈ D.leftSupport
  · by_cases hj : j ∈ D.rightSupport
    · simp [hi, hj]
    · have hright : D.rightVec j = 0 := D.right_zero_outside j hj
      simp [hi, hj, hright]
  · have hleft : D.leftVec i = 0 := D.left_zero_outside i hi
    by_cases hj : j ∈ D.rightSupport
    · simp [hi, hj, hleft]
    · simp [hi, hj, hleft]

lemma supported_term_eq_cut_flux (D : C1CutFluxData) (i j : D.ι) :
    (if i ∈ D.leftSupport ∧ j ∈ D.rightSupport then
      D.leftVec i * D.A1 i j * D.rightVec j
    else 0) =
      if i ∈ D.leftSupport ∧ j ∈ D.rightSupport ∧ ¬ (i ∈ D.core ∧ j ∈ D.core) then
        D.leftVec i * D.A1 i j * D.rightVec j
      else 0 := by
  by_cases hs : i ∈ D.leftSupport ∧ j ∈ D.rightSupport
  · by_cases hcore : i ∈ D.core ∧ j ∈ D.core
    · have hA1 : D.A1 i j = 0 := D.zero_core_block i hcore.1 j hcore.2
      simp [hs, hcore, hA1]
    · simp [hs, hcore]
  · by_cases hi : i ∈ D.leftSupport
    · by_cases hj : j ∈ D.rightSupport
      · exfalso
        exact hs ⟨hi, hj⟩
      · simp [hi, hj]
    · simp [hi]

end C1CutFluxData

open C1CutFluxData

/-- Paper label: `prop:c1-cut-flux`. The bilinear response `lᵀ A₁ r` can be restricted to the
supports of the left/right Perron vectors, and because the `core → core` block of `A₁` vanishes,
the remaining terms are exactly the weighted cut-flux contributions. -/
theorem paper_c1_cut_flux (D : C1CutFluxData) :
    D.firstOrderResponseLaw ∧ D.cutFluxRestriction := by
  refine ⟨?_, ?_⟩
  · unfold C1CutFluxData.firstOrderResponseLaw C1CutFluxData.firstOrderResponse
      C1CutFluxData.supportedResponse
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact D.firstOrder_term_eq_supported i j
  · unfold C1CutFluxData.cutFluxRestriction C1CutFluxData.supportedResponse C1CutFluxData.cutFlux
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    exact D.supported_term_eq_cut_flux i j

end

end Omega.SyncKernelWeighted
