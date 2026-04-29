import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbkPadeJacobiIdentity

namespace Omega.Zeta

/-- Concrete finite-local RH-blindness package for
`thm:xi-time-part9zbh-foldpi-finite-local-rh-blindness`.

Each finite-depth datum matching the fold-`π` even-zeta prefix through order `2n` factors through
the canonical finite Padé-Jacobi shadow, and consequently no finite such datum can witness a
distinct RH-sensitive shadow at that level. -/
def xi_time_part9zbh_foldpi_finite_local_rh_blindness_statement : Prop :=
  (∀ n : ℕ, 1 ≤ n → IsUniquePadeJacobiShadow m_phi (m_phi_n n) n) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ R : PadeJacobiShadow,
      finiteDepth R → matchesToOrder m_phi R (2 * n) →
        (∃ pref : PadeJacobiShadow, pref = m_phi_n n ∧ R = pref) ∧
          ¬ R ≠ m_phi_n n) ∧
    (∀ n : ℕ, 1 ≤ n → ∀ R : PadeJacobiShadow,
      finiteDepth R → matchesToOrder m_phi R (2 * n) → ¬ R ≠ m_phi_n n)

/-- Paper label: `thm:xi-time-part9zbh-foldpi-finite-local-rh-blindness`. -/
theorem paper_xi_time_part9zbh_foldpi_finite_local_rh_blindness :
    xi_time_part9zbh_foldpi_finite_local_rh_blindness_statement := by
  refine ⟨?_, ?_, ?_⟩
  · intro n hn
    exact paper_xi_time_part9zbk_pade_jacobi_identity n hn
  · intro n hn R hFinite hMatch
    have hR : R = m_phi_n n :=
      paper_xi_time_part9zbk_pade_jacobi_identity n hn R hFinite hMatch
    exact ⟨⟨m_phi_n n, rfl, hR⟩, fun hne => hne hR⟩
  · let dependsOnFiniteData : (ℕ × PadeJacobiShadow) → ℕ → Prop :=
      fun I D => D = I.1 ∧ 1 ≤ I.1 ∧ finiteDepth I.2 ∧
        matchesToOrder m_phi I.2 (2 * I.1)
    let rhEquivalent : (ℕ × PadeJacobiShadow) → Prop :=
      fun I => I.2 ≠ m_phi_n I.1
    have hfiniteBlind :
        ∀ I D, dependsOnFiniteData I D → ¬ rhEquivalent I := by
      intro I D hData hne
      exact hne
        (paper_xi_time_part9zbk_pade_jacobi_identity I.1 hData.2.1 I.2 hData.2.2.1
          hData.2.2.2)
    intro n hn R hFinite hMatch
    exact hfiniteBlind (n, R) n ⟨rfl, hn, hFinite, hMatch⟩

end Omega.Zeta
