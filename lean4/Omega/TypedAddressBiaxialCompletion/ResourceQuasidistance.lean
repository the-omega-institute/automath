import Mathlib.Data.ENNReal.Operations

namespace Omega.TypedAddressBiaxialCompletion

universe u v

/-- Minimal certificate interface for the resource quasidistance. A certificate from `p` to `q`
    carries a pointwise nonnegative resource budget vector, a zero-budget self certificate, and a
    composition rule with pointwise budget control. -/
structure ResourceQuasidistanceCertificateInterface (State : Type u) (Axis : Type v) where
  Certificate : State → State → Type*
  budget : {p q : State} → Certificate p q → Axis → ENNReal
  scalarize : (Axis → ENNReal) → ENNReal
  scalarize_zero : scalarize (0 : Axis → ENNReal) = 0
  scalarize_mono :
    ∀ {b₁ b₂ : Axis → ENNReal}, (∀ a, b₁ a ≤ b₂ a) → scalarize b₁ ≤ scalarize b₂
  scalarize_subadd :
    ∀ b₁ b₂ : Axis → ENNReal, scalarize (fun a => b₁ a + b₂ a) ≤ scalarize b₁ + scalarize b₂
  selfCert : ∀ p : State, Certificate p p
  self_budget_zero : ∀ p : State, budget (selfCert p) = (0 : Axis → ENNReal)
  comp : ∀ {p q r : State}, Certificate p q → Certificate q r → Certificate p r
  comp_budget_le :
    ∀ {p q r : State} (c₁ : Certificate p q) (c₂ : Certificate q r),
      ∀ a, budget (comp c₁ c₂) a ≤ budget c₁ a + budget c₂ a
  cert_nonempty : ∀ p q : State, Nonempty (Certificate p q)

/-- Scalarized budget of a certificate. -/
def scalarizedBudget
    {State : Type u} {Axis : Type v}
    (I : ResourceQuasidistanceCertificateInterface State Axis)
    {p q : State} (c : I.Certificate p q) : ENNReal :=
  I.scalarize (I.budget c)

/-- The resource quasidistance is the infimum of the scalarized budgets of all comparison
    certificates. -/
noncomputable def resourceQuasidistance
    {State : Type u} {Axis : Type v}
    (I : ResourceQuasidistanceCertificateInterface State Axis) (p q : State) : ENNReal :=
  ⨅ c : I.Certificate p q, scalarizedBudget I c

theorem resourceQuasidistance_refl
    {State : Type u} {Axis : Type v}
    (I : ResourceQuasidistanceCertificateInterface State Axis) (p : State) :
    resourceQuasidistance I p p = 0 := by
  letI : Nonempty (I.Certificate p p) := I.cert_nonempty p p
  apply le_antisymm
  · calc
      resourceQuasidistance I p p ≤ scalarizedBudget I (I.selfCert p) := by
        unfold resourceQuasidistance
        exact iInf_le (fun c : I.Certificate p p => scalarizedBudget I c) (I.selfCert p)
      _ = I.scalarize (0 : Axis → ENNReal) := by
        simp [scalarizedBudget, I.self_budget_zero p]
      _ = 0 := I.scalarize_zero
  · exact bot_le

theorem resourceQuasidistance_triangle
    {State : Type u} {Axis : Type v}
    (I : ResourceQuasidistanceCertificateInterface State Axis) (p q r : State) :
    resourceQuasidistance I p r ≤ resourceQuasidistance I p q + resourceQuasidistance I q r := by
  letI : Nonempty (I.Certificate p q) := I.cert_nonempty p q
  letI : Nonempty (I.Certificate q r) := I.cert_nonempty q r
  refine ENNReal.le_iInf_add_iInf ?_
  intro c₁ c₂
  have hcomp :
      resourceQuasidistance I p r ≤ scalarizedBudget I (I.comp c₁ c₂) := by
    unfold resourceQuasidistance
    exact iInf_le (fun c : I.Certificate p r => scalarizedBudget I c) (I.comp c₁ c₂)
  have hscalar :
      scalarizedBudget I (I.comp c₁ c₂) ≤ scalarizedBudget I c₁ + scalarizedBudget I c₂ := by
    exact le_trans
      (I.scalarize_mono (I.comp_budget_le c₁ c₂))
      (I.scalarize_subadd (I.budget c₁) (I.budget c₂))
  exact le_trans hcomp hscalar

/-- Paper-facing package: zero-budget self certificates give `d_res(p,p)=0`, and certificate
    composition together with monotone subadditive scalarization yields the triangle inequality.
    prop:typed-address-biaxial-completion-resource-quasidistance -/
theorem paper_typed_address_biaxial_completion_resource_quasidistance
    {State : Type u} {Axis : Type v}
    (I : ResourceQuasidistanceCertificateInterface State Axis) :
    (∀ p : State, resourceQuasidistance I p p = 0) ∧
      ∀ p q r : State,
        resourceQuasidistance I p r ≤ resourceQuasidistance I p q + resourceQuasidistance I q r := by
  exact ⟨resourceQuasidistance_refl I, resourceQuasidistance_triangle I⟩

end Omega.TypedAddressBiaxialCompletion
