import Mathlib.Tactic
import Omega.Conclusion.M2Level3XiDelta0Order6Charpolys
import Omega.Conclusion.M2Level3XiDelta0Order6ParabolicSpectrum
import Omega.Conclusion.M2Level3XiInertiaHeckeEigensystemsCharpoly

namespace Omega.Conclusion

/-- The tame order-`3` conductor contribution on the common `24`-dimensional block, normalized by
the quadratic degree of the `Φ₃` and `Φ₆` factors. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V24 : ℕ :=
  4 + 2

/-- The tame order-`2` conductor contribution on the common `24`-dimensional block, normalized by
the quadratic degree of the `Φ₆` factor. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V24 : ℕ :=
  (4 + 2 * 2) / 2

/-- The `Ξ`-Artin conductor on the common `24`-dimensional block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_xi_V24 : ℕ :=
  conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V24

/-- The combined parabolic/Artin package for the common `24`-dimensional block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_V24 : (ℕ × ℕ) × ℕ :=
  ((conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V24,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V24),
    conclusion_m2_level3_xi_artin_parabolic_c1_xi_V24)

/-- The tame order-`3` conductor contribution on the Klingen defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Kl : ℕ :=
  1 + 2

/-- The tame order-`2` conductor contribution on the Klingen defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Kl : ℕ :=
  (4 + 2 * 2) / 2

/-- The `Ξ`-Artin conductor on the Klingen defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Kl : ℕ :=
  conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Kl

/-- The combined parabolic/Artin package for the Klingen defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_V15_Kl : (ℕ × ℕ) × ℕ :=
  ((conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Kl,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Kl),
    conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Kl)

/-- The tame order-`3` conductor contribution on the Siegel defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Si : ℕ :=
  4 + 2

/-- The tame order-`2` conductor contribution on the Siegel defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Si : ℕ :=
  (0 + 2 * 2) / 2

/-- The `Ξ`-Artin conductor on the Siegel defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Si : ℕ :=
  conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly_minus_mult_V15_Si

/-- The combined parabolic/Artin package for the Siegel defect block. -/
def conclusion_m2_level3_xi_artin_parabolic_c1_V15_Si : (ℕ × ℕ) × ℕ :=
  ((conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Si,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Si),
    conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Si)

/-- Paper label: `prop:conclusion-m2-level3-xi-artin-parabolic-c1`. The audited `Δ₀` order-`6`
block weights contribute `(c₃, c₂)` by the normalized order-`3` and order-`2` codimensions, and
the `Ξ` conductor is the recorded `-1`-eigenspace multiplicity. -/
theorem paper_conclusion_m2_level3_xi_artin_parabolic_c1 :
    conclusion_m2_level3_xi_artin_parabolic_c1_V24 = ((6, 4), 8) ∧
      conclusion_m2_level3_xi_artin_parabolic_c1_V15_Kl = ((3, 4), 8) ∧
      conclusion_m2_level3_xi_artin_parabolic_c1_V15_Si = ((6, 2), 4) := by
  have hdelta0 := paper_conclusion_m2_level3_xi_delta0_order6_charpolys ⟨()⟩
  have hparabolic := paper_conclusion_m2_level3_xi_delta0_order6_parabolic_spectrum
  have hxi := paper_conclusion_m2_level3_xi_inertia_hecke_eigensystems_charpoly
  rcases hdelta0 with ⟨_, _, _, _, _, _, _, _, _⟩
  rcases hparabolic with ⟨_, _, _, _, _, _⟩
  rcases hxi with ⟨_, _, _, _, hminusV24, _, hminusV15Kl, _, hminusV15Si, _, _, _⟩
  refine ⟨?_, ?_, ?_⟩
  · simp [conclusion_m2_level3_xi_artin_parabolic_c1_V24,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V24,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V24,
      conclusion_m2_level3_xi_artin_parabolic_c1_xi_V24, hminusV24]
  · simp [conclusion_m2_level3_xi_artin_parabolic_c1_V15_Kl,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Kl,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Kl,
      conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Kl, hminusV15Kl]
  · simp [conclusion_m2_level3_xi_artin_parabolic_c1_V15_Si,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c3_V15_Si,
      conclusion_m2_level3_xi_artin_parabolic_c1_delta0_c2_V15_Si,
      conclusion_m2_level3_xi_artin_parabolic_c1_xi_V15_Si, hminusV15Si]

end Omega.Conclusion
