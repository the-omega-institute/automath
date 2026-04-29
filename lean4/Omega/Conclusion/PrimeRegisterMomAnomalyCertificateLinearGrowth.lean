import Omega.POM.AnomSwapLowerboundAndMomAmplify

namespace Omega.Conclusion

/-- Conclusion-level wrapper for the MOM-amplified anomaly-swap certificate lower bound. -/
def conclusion_prime_register_mom_anomaly_certificate_linear_growth_statement
    {W E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (Anom : W → E) (MOM : ℕ → W → W) : Prop :=
  ∀ q s : ℕ, ∀ label : E, ∀ w : W,
    0 < ‖label‖ →
      Anom (MOM q w) = Omega.POM.anomSwapTotal s label →
        Anom (MOM q w) = (q : ℝ) • Anom w →
          q * ‖Anom w‖ / ‖label‖ ≤ s

/-- Paper label: `thm:conclusion-prime-register-mom-anomaly-certificate-linear-growth`. -/
theorem paper_conclusion_prime_register_mom_anomaly_certificate_linear_growth
    {W E : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
    (Anom : W → E) (MOM : ℕ → W → W) :
    conclusion_prime_register_mom_anomaly_certificate_linear_growth_statement Anom MOM := by
  exact (Omega.POM.paper_pom_anom_swap_lowerbound_and_mom_amplify Anom MOM).2.2.2

end Omega.Conclusion
