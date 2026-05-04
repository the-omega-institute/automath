import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete endpoint-jet data for the three-term coefficient package. -/
structure xi_endpoint_local_jet_inversion_data where
  f0 : ℝ
  f2 : ℝ
  f4 : ℝ

/-- The leading endpoint coefficient. -/
noncomputable def xi_endpoint_local_jet_inversion_A
    (D : xi_endpoint_local_jet_inversion_data) : ℝ :=
  2 * Real.sqrt Real.pi * D.f0

/-- The second endpoint coefficient. -/
noncomputable def xi_endpoint_local_jet_inversion_B
    (D : xi_endpoint_local_jet_inversion_data) : ℝ :=
  Real.sqrt Real.pi * (2 * D.f2 - (1 / 4 : ℝ) * D.f0)

/-- The third endpoint coefficient. -/
noncomputable def xi_endpoint_local_jet_inversion_C
    (D : xi_endpoint_local_jet_inversion_data) : ℝ :=
  Real.sqrt Real.pi * (D.f4 - (5 / 4 : ℝ) * D.f2 + (1 / 64 : ℝ) * D.f0)

/-- The triangular inversion formulas determined by the three endpoint coefficients. -/
def xi_endpoint_local_jet_inversion_data.Holds
    (D : xi_endpoint_local_jet_inversion_data) : Prop :=
  xi_endpoint_local_jet_inversion_A D / (2 * Real.sqrt Real.pi) = D.f0 ∧
    (xi_endpoint_local_jet_inversion_B D / Real.sqrt Real.pi + (1 / 4 : ℝ) * D.f0) / 2 =
      D.f2 ∧
      xi_endpoint_local_jet_inversion_C D / Real.sqrt Real.pi +
          (5 / 4 : ℝ) * D.f2 - (1 / 64 : ℝ) * D.f0 =
        D.f4

/-- Paper label: `cor:xi-endpoint-local-jet-inversion`. -/
theorem paper_xi_endpoint_local_jet_inversion
    (D : xi_endpoint_local_jet_inversion_data) : D.Holds := by
  have hsqrt_ne : Real.sqrt Real.pi ≠ 0 := by
    exact (Real.sqrt_pos.2 Real.pi_pos).ne'
  refine ⟨?_, ?_, ?_⟩
  · unfold xi_endpoint_local_jet_inversion_A
    field_simp [hsqrt_ne]
  · unfold xi_endpoint_local_jet_inversion_B
    field_simp [hsqrt_ne]
    ring_nf
  · unfold xi_endpoint_local_jet_inversion_C
    field_simp [hsqrt_ne]
    ring_nf

end Omega.Zeta
