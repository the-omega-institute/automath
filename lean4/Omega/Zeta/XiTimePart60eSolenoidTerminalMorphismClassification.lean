import Omega.Zeta.XiCdimLocalizationSolenoidContinuousHomClassification

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part60e-solenoid-terminal-morphism-classification`. -/
theorem paper_xi_time_part60e_solenoid_terminal_morphism_classification
    (S T : Finset ℕ) :
    XiCdimLocalizationSolenoidContinuousHomClassification T S ∧
      ((∃ φ : XiLocalizedSolenoidContinuousHomModel T S,
          localizedCrossHomScalar φ ≠ 0) → S ⊆ T) ∧
        (S ⊆ T →
          ∀ φ : XiLocalizedSolenoidContinuousHomModel T S,
            localizedCrossHomScalar φ ≠ 0 → xiLocalizedDiscreteMapInjective φ) := by
  rcases paper_xi_cdim_localization_solenoid_continuous_hom_classification T S with
    hClass
  rcases hClass with ⟨_hSubset, hNotSubset, hInjective⟩
  refine ⟨paper_xi_cdim_localization_solenoid_continuous_hom_classification T S, ?_, ?_⟩
  · rintro ⟨φ, hφ⟩
    by_contra hST
    have hzero : φ.1 (1 : LocalizedIntegerGroup S) = 0 := hNotSubset hST φ 1
    exact hφ (by simpa [localizedCrossHomScalar] using hzero)
  · intro hST φ hφ
    exact hInjective hST φ hφ

end Omega.Zeta
