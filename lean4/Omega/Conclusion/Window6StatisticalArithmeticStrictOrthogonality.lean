import Mathlib.NumberTheory.Real.GoldenRatio
import Omega.Zeta.LocalizedIntegersNoUniformFinitelyGeneratedLedger
import Omega.Zeta.XiTimePart9saUniformBaselineFixedBinaryExperiment

namespace Omega.Conclusion

/-- Concrete asymptotic sufficiency witness carried by the last-bit Bernoulli experiment. -/
def conclusion_window6_statistical_arithmetic_strict_orthogonality_lastbit_sufficient : Prop :=
  ∀ m : ℕ,
    Omega.Zeta.xiFoldLastbitStatisticalSufficiency
      (Omega.Folding.foldBinTwoAtomLimitMass false + Omega.Folding.foldBinTwoAtomLimitMass true)
      (Omega.Folding.foldBinTwoAtomLimitMass false + Omega.Folding.foldBinTwoAtomLimitMass true)
      (Omega.Folding.foldBinTwoAtomLimitMass false + Omega.Folding.foldBinTwoAtomLimitMass true)
      0 0 Real.goldenRatio m

/-- Global Smith-style completion would require a uniform finite recovery bound from the
arithmetized ledger channel. -/
def conclusion_window6_statistical_arithmetic_strict_orthogonality_smith_complete : Prop :=
  ∃ F : ℕ → ℕ, ∀ S : Omega.Zeta.FinitePrimeLocalization,
    S.card ≤ F (Omega.Zeta.localizedIntegersCircleDimension S)

/-- Paper label: `thm:conclusion-window6-statistical-arithmetic-strict-orthogonality`.
The window-6 last-bit experiment already gives an asymptotically sufficient one-bit statistic for
the Bernoulli escort parameter, while the arithmetic completion channel admits no uniform finite
ledger bound. Hence no single statistic built from the one-bit count together with a fixed finite
ledger can be both asymptotically sufficient and globally complete for Smith recovery. -/
def conclusion_window6_statistical_arithmetic_strict_orthogonality_statement : Prop :=
  conclusion_window6_statistical_arithmetic_strict_orthogonality_lastbit_sufficient ∧
    ((conclusion_window6_statistical_arithmetic_strict_orthogonality_lastbit_sufficient ∧
        conclusion_window6_statistical_arithmetic_strict_orthogonality_smith_complete) →
      False)

theorem paper_conclusion_window6_statistical_arithmetic_strict_orthogonality :
    conclusion_window6_statistical_arithmetic_strict_orthogonality_statement := by
  have hsuff : conclusion_window6_statistical_arithmetic_strict_orthogonality_lastbit_sufficient := by
    simpa [conclusion_window6_statistical_arithmetic_strict_orthogonality_lastbit_sufficient] using
      Omega.Zeta.paper_xi_time_part9sa_uniform_baseline_fixed_binary_experiment_true.2
  refine ⟨hsuff, ?_⟩
  intro h
  exact Omega.Zeta.paper_xi_localized_integers_no_uniform_finitely_generated_ledger h.2

end Omega.Conclusion
