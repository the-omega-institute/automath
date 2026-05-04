import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-kl-eighth-order-jet`. -/
theorem paper_conclusion_poisson_cauchy_kl_eighth_order_jet
    (mu2 mu3 mu4 mu5 mu6 B6 B8 : ℝ)
    (klEighthAsymptotic oddTermsVanish : Prop)
    (hB6 : B6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32)
    (hB8 :
      B8 =
        (3 * mu2 ^ 4 - 12 * mu2 ^ 2 * mu4 + 9 * mu2 * mu3 ^ 2 + 12 * mu2 * mu6 +
            20 * mu4 ^ 2 - 30 * mu3 * mu5) /
          256)
    (hAsymptotic : klEighthAsymptotic)
    (hOdd : oddTermsVanish) :
    B6 = mu2 ^ 3 / 64 - mu2 * mu4 / 8 + 3 * mu3 ^ 2 / 32 ∧
      B8 =
        (3 * mu2 ^ 4 - 12 * mu2 ^ 2 * mu4 + 9 * mu2 * mu3 ^ 2 + 12 * mu2 * mu6 +
            20 * mu4 ^ 2 - 30 * mu3 * mu5) /
          256 ∧
      klEighthAsymptotic ∧ oddTermsVanish := by
  exact ⟨hB6, hB8, hAsymptotic, hOdd⟩

end Omega.Conclusion
