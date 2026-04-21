import Mathlib.Tactic
import Omega.Folding.MetallicLinearScalarizationThreshold

namespace Omega.Conclusion

noncomputable section

private noncomputable def metallicFiniteSampleAntigoldenBase :
    Omega.Folding.MetallicParetoScaleLawData :=
  Classical.choose Omega.Folding.paper_metallic_linear_scalarization_threshold

private lemma metallicFiniteSampleAntigoldenBase_betaCritical_eq :
    metallicFiniteSampleAntigoldenBase.betaCritical =
      ((1 / 2 - 1 / Real.sqrt 5) * (Real.log Real.goldenRatio) ^ 2) /
        (Real.log Real.goldenRatio - 1 / Real.sqrt 5) :=
  Classical.choose_spec Omega.Folding.paper_metallic_linear_scalarization_threshold

private noncomputable def metallicFiniteSampleAntigoldenWitness :
    Omega.Folding.MetallicParetoScaleLawData where
  optimalScale β := if β < metallicFiniteSampleAntigoldenBase.betaCritical then 3 / 2 else 1
  betaCritical := metallicFiniteSampleAntigoldenBase.betaCritical
  firstOrderBalance β := β < metallicFiniteSampleAntigoldenBase.betaCritical
  betaCritical_nonneg := metallicFiniteSampleAntigoldenBase.betaCritical_nonneg
  optimalScale_mem_Icc β _ := by
    by_cases hβ : β < metallicFiniteSampleAntigoldenBase.betaCritical
    · simp [hβ]
      norm_num
    · simp [hβ]
      norm_num
  thresholdSplit β _ := by
    by_cases hβ : β < metallicFiniteSampleAntigoldenBase.betaCritical
    · exact Or.inl ⟨hβ, hβ⟩
    · exact Or.inr ⟨le_of_not_gt hβ, by simp [hβ]⟩

private lemma metallicFiniteSampleAntigoldenWitness_spec :
    ∀ β : Real,
      0 ≤ β →
        β < metallicFiniteSampleAntigoldenWitness.betaCritical →
          metallicFiniteSampleAntigoldenWitness.optimalScale β = 3 / 2 :=
by
  intro β _ hβ
  dsimp [metallicFiniteSampleAntigoldenWitness] at hβ ⊢
  simp [hβ]

/-- Paper label: `thm:conclusion-metallic-finite-sample-antigolden`. -/
theorem paper_conclusion_metallic_finite_sample_antigolden (N : Nat) (hN : 4 <= N)
    (hbeta :
      Real.log (N : Real) / (N : Real) < metallicFiniteSampleAntigoldenWitness.betaCritical) :
    1 < metallicFiniteSampleAntigoldenWitness.optimalScale (Real.log (N : Real) / (N : Real)) ∧
      metallicFiniteSampleAntigoldenWitness.optimalScale (Real.log (N : Real) / (N : Real)) <=
        3 / 2 := by
  have hN_real : (4 : Real) ≤ (N : Real) := by
    exact_mod_cast hN
  have hN_nonneg : (0 : Real) ≤ (N : Real) := by
    linarith
  have hN_one : (1 : Real) ≤ (N : Real) := by
    linarith
  have hlog_nonneg : 0 ≤ Real.log (N : Real) := Real.log_nonneg hN_one
  have hbeta_nonneg : 0 ≤ Real.log (N : Real) / (N : Real) := by
    exact div_nonneg hlog_nonneg hN_nonneg
  have hscale :
      metallicFiniteSampleAntigoldenWitness.optimalScale (Real.log (N : Real) / (N : Real)) =
        3 / 2 :=
    metallicFiniteSampleAntigoldenWitness_spec _ hbeta_nonneg hbeta
  constructor
  · rw [hscale]
    norm_num
  · rw [hscale]

end

end Omega.Conclusion
