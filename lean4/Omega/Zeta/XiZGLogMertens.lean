import Omega.Zeta.XiZGReciprocalHarmonicAsymptotic

namespace Omega.Zeta

/-- Paper label: `thm:xi-zg-log-mertens`. -/
theorem paper_xi_zg_log_mertens (D : Omega.Zeta.XiZGReciprocalHarmonicData) :
    D.residueAtOne = D.deltaZG ∧
      (∀ ε > 0, ε < 1 / 2 → ∃ C_ZG : ℝ, ∀ X ≥ 1,
        |D.reciprocalSum X - (D.deltaZG * Real.log X + C_ZG)| ≤
          D.errorConstant ε * Real.rpow X (-1 / 2 + ε)) := by
  exact ⟨D.residue_eq_delta, paper_xi_zg_reciprocal_harmonic_asymptotic D⟩

end Omega.Zeta
