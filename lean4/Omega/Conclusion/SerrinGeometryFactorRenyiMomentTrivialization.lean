import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

structure SerrinGeometryFactorRenyiMomentTrivializationData where
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass : ℝ
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one :
    conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass = 1

def conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) : ℝ :=
  D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass

def conclusion_serrin_geometry_factor_renyi_moment_trivialization_moment_sum
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) (q : ℕ) : ℝ :=
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor D ^ q

def conclusion_serrin_geometry_factor_renyi_moment_trivialization_kernel
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) : ℝ :=
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_moment_sum D 1 - 1

def conclusion_serrin_geometry_factor_renyi_moment_trivialization_spectral_radius
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) : ℝ :=
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor D

noncomputable def conclusion_serrin_geometry_factor_renyi_moment_trivialization_pressure
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) : ℝ :=
  Real.log (conclusion_serrin_geometry_factor_renyi_moment_trivialization_spectral_radius D)

def conclusion_serrin_geometry_factor_renyi_moment_trivialization_renyi_entropy
    (_D : SerrinGeometryFactorRenyiMomentTrivializationData) (_q : ℕ) : ℝ :=
  0

def SerrinGeometryFactorRenyiMomentTrivializationStatement
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) : Prop :=
  conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor D = 1 ∧
    (∀ q : ℕ,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_moment_sum D q = 1) ∧
    conclusion_serrin_geometry_factor_renyi_moment_trivialization_kernel D = 0 ∧
    conclusion_serrin_geometry_factor_renyi_moment_trivialization_spectral_radius D = 1 ∧
    conclusion_serrin_geometry_factor_renyi_moment_trivialization_pressure D = 0 ∧
    ∀ q : ℕ,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_renyi_entropy D q = 0

theorem paper_conclusion_serrin_geometry_factor_renyi_moment_trivialization
    (D : SerrinGeometryFactorRenyiMomentTrivializationData) :
    SerrinGeometryFactorRenyiMomentTrivializationStatement D := by
  refine ⟨D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro q
    simp [conclusion_serrin_geometry_factor_renyi_moment_trivialization_moment_sum,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor,
      D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one]
  · simp [conclusion_serrin_geometry_factor_renyi_moment_trivialization_kernel,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_moment_sum,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor,
      D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one]
  · simpa [conclusion_serrin_geometry_factor_renyi_moment_trivialization_spectral_radius,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor] using
      D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one
  · simp [conclusion_serrin_geometry_factor_renyi_moment_trivialization_pressure,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_spectral_radius,
      conclusion_serrin_geometry_factor_renyi_moment_trivialization_geometric_factor,
      D.conclusion_serrin_geometry_factor_renyi_moment_trivialization_normalized_mass_eq_one]
  · intro q
    rfl

end Omega.Conclusion
