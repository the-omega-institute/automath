import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- The cubic Perron-branch equation `F(λ,u) = 0`. -/
def vectorPotentialPhiMinusCubic (lam u : ℝ) : ℝ :=
  lam ^ 3 - (u + 2) * lam ^ 2 + (u - 2) * lam + 3 * u

/-- The parameterized `u(λ)` branch obtained by solving the cubic linearly in `u`. -/
def vectorPotentialPhiMinusU (lam : ℝ) : ℝ :=
  lam * (lam ^ 2 - 2 * lam - 2) / (lam ^ 2 - lam - 3)

/-- The `u`-substituted implicit-derivative formula for `α(λ)`. -/
def vectorPotentialPhiMinusAlphaImplicit (lam : ℝ) : ℝ :=
  ((lam ^ 2 - 2 * lam - 2) * (lam ^ 2 - lam - 3)) /
    (lam ^ 4 - 2 * lam ^ 3 - 5 * lam ^ 2 + 12 * lam + 6)

/-- The closed rational parametrization of the slope. -/
def vectorPotentialPhiMinusAlphaClosed (lam : ℝ) : ℝ :=
  (lam ^ 4 - 3 * lam ^ 3 - 3 * lam ^ 2 + 8 * lam + 6) /
    (lam ^ 4 - 2 * lam ^ 3 - 5 * lam ^ 2 + 12 * lam + 6)

/-- The centered Legendre-value expression `θα - (P(θ) - P(0))` with `θ = log u`
and `P(0) = log 3`. -/
def vectorPotentialPhiMinusRate (lam : ℝ) : ℝ :=
  vectorPotentialPhiMinusAlphaClosed lam * Real.log (vectorPotentialPhiMinusU lam) -
    (Real.log lam - Real.log 3)

/-- Concrete algebraic data needed for the parametrized branch formulas. -/
structure VectorPotentialPhiMinusLdpParamData where
  lam : ℝ
  hUdenom : lam ^ 2 - lam - 3 ≠ 0
  hAlphaDenom : lam ^ 4 - 2 * lam ^ 3 - 5 * lam ^ 2 + 12 * lam + 6 ≠ 0

namespace VectorPotentialPhiMinusLdpParamData

/-- The cubic vanishes after solving linearly for `u(λ)`. -/
def closedFormU (D : VectorPotentialPhiMinusLdpParamData) : Prop :=
  vectorPotentialPhiMinusU D.lam * (D.lam ^ 2 - D.lam - 3) =
    D.lam * (D.lam ^ 2 - 2 * D.lam - 2)

/-- The implicit-derivative slope equals the closed rational parametrization. -/
def closedFormAlpha (D : VectorPotentialPhiMinusLdpParamData) : Prop :=
  vectorPotentialPhiMinusAlphaImplicit D.lam = vectorPotentialPhiMinusAlphaClosed D.lam

/-- The Legendre value is the stated logarithmic closed form. -/
def closedFormRate (D : VectorPotentialPhiMinusLdpParamData) : Prop :=
  vectorPotentialPhiMinusRate D.lam =
    vectorPotentialPhiMinusAlphaClosed D.lam * Real.log (vectorPotentialPhiMinusU D.lam) -
      Real.log D.lam + Real.log 3

end VectorPotentialPhiMinusLdpParamData

open VectorPotentialPhiMinusLdpParamData

/-- Paper label: `prop:vector-potential-phi-minus-ldp-param`. -/
theorem paper_sync_kernel_vector_potential_phi_minus_ldp_param
    (D : VectorPotentialPhiMinusLdpParamData) :
    D.closedFormU ∧ D.closedFormAlpha ∧ D.closedFormRate := by
  refine ⟨?_, ?_, ?_⟩
  · unfold VectorPotentialPhiMinusLdpParamData.closedFormU
    let d : ℝ := D.lam ^ 2 - D.lam - 3
    change D.lam * (D.lam ^ 2 - 2 * D.lam - 2) / d * d =
      D.lam * (D.lam ^ 2 - 2 * D.lam - 2)
    have hd : d ≠ 0 := by
      simpa [d] using D.hUdenom
    calc
      D.lam * (D.lam ^ 2 - 2 * D.lam - 2) / d * d =
          D.lam * (D.lam ^ 2 - 2 * D.lam - 2) * d / d := by
            rw [div_mul_eq_mul_div]
      _ = D.lam * (D.lam ^ 2 - 2 * D.lam - 2) := by
            calc
              D.lam * (D.lam ^ 2 - 2 * D.lam - 2) * d / d =
                  d * ((D.lam * (D.lam ^ 2 - 2 * D.lam - 2)) / d) := by
                    ring
              _ = D.lam * (D.lam ^ 2 - 2 * D.lam - 2) := by
                    simpa [mul_comm, mul_left_comm, mul_assoc] using
                      (mul_div_cancel₀ (D.lam * (D.lam ^ 2 - 2 * D.lam - 2)) hd)
  · unfold VectorPotentialPhiMinusLdpParamData.closedFormAlpha
    dsimp [vectorPotentialPhiMinusAlphaImplicit, vectorPotentialPhiMinusAlphaClosed]
    field_simp [D.hAlphaDenom]
    ring_nf
  · unfold VectorPotentialPhiMinusLdpParamData.closedFormRate
    dsimp [vectorPotentialPhiMinusRate]
    ring_nf

/-- Paper label: `prop:vector-potential-phi-minus-ldp-param`. -/
theorem paper_vector_potential_phi_minus_ldp_param (D : VectorPotentialPhiMinusLdpParamData) :
    D.closedFormU ∧ D.closedFormAlpha ∧ D.closedFormRate := by
  exact paper_sync_kernel_vector_potential_phi_minus_ldp_param D

end

end Omega.SyncKernelWeighted
