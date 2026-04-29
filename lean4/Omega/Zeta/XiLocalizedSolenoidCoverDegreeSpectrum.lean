import Omega.Zeta.LocalizedSolenoidNonzeroEndomorphismFiniteCoverDegree

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-solenoid-cover-degree-spectrum`. -/
theorem paper_xi_localized_solenoid_cover_degree_spectrum (S : FinitePrimeLocalization) :
    (∀ d : ℕ, 0 < d →
        ((∃ n : ℕ, xi_localized_solenoid_multiplication_kernel_degree_coverDegree S n = d) ↔
          localizedIndex S d = d)) ∧
      (∀ n : ℕ, 0 < n →
        (xi_localized_solenoid_multiplication_kernel_degree_coverDegree S n = 1 ↔
          localizedIndex S n = 1)) := by
  constructor
  · intro d _hd
    constructor
    · rintro ⟨n, hn⟩
      unfold xi_localized_solenoid_multiplication_kernel_degree_coverDegree localizedIndex nSperp at hn
      unfold localizedIndex nSperp
      by_cases hnS : n ∈ S
      · simp [hnS] at hn
        subst d
        by_cases h1S : 1 ∈ S <;> simp [h1S]
      · simp [hnS] at hn
        subst d
        simp [hnS]
    · intro hd
      exact ⟨d, by simp [xi_localized_solenoid_multiplication_kernel_degree_coverDegree, hd]⟩
  · intro n _hn
    rfl

end Omega.Zeta
