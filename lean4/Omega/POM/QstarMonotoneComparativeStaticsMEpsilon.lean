import Mathlib.Data.Real.Basic

namespace Omega.POM

/-- Paper label: `cor:pom-qstar-monotone-comparative-statics-m-epsilon`. Monotonicity of
`qstar` in the abstract scale parameter composes with the finite-design monotonicities of
`lambda` in sample size and tolerance. -/
theorem paper_pom_qstar_monotone_comparative_statics_m_epsilon (qstar : ℝ → ℕ)
    (hmono : ∀ {lam mu : ℝ}, lam ≤ mu → qstar lam ≤ qstar mu) (lambda : ℕ → ℝ → ℝ)
    (hm : ∀ {m1 m2 ε}, m1 ≤ m2 → lambda m2 ε ≤ lambda m1 ε)
    (heps : ∀ {m ε1 ε2}, ε1 ≤ ε2 → lambda m ε2 ≤ lambda m ε1) :
    (∀ {m1 m2 ε}, m1 ≤ m2 → qstar (lambda m2 ε) ≤ qstar (lambda m1 ε)) ∧
      (∀ {m ε1 ε2}, ε1 ≤ ε2 → qstar (lambda m ε2) ≤ qstar (lambda m ε1)) := by
  exact ⟨fun hle => hmono (hm hle), fun hle => hmono (heps hle)⟩

end Omega.POM
