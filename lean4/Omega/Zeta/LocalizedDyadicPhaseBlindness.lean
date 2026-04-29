import Omega.Zeta.CdimLocalizationZetaAS

namespace Omega.Zeta

/-- Paper label: `cor:xi-localized-dyadic-phase-blindness`.
The dyadic prime-power coefficient depends only on whether `2` belongs to the support. -/
theorem paper_xi_localized_dyadic_phase_blindness (S T : Finset ℕ) (a : ℕ)
    (h2 : (2 ∈ S ↔ 2 ∈ T)) :
    xiLocalizedCoeff S (2 ^ a) = xiLocalizedCoeff T (2 ^ a) := by
  have hS := xiLocalizedCoeff_prime_pow S (p := 2) (k := a) (by norm_num : Nat.Prime 2)
  have hT := xiLocalizedCoeff_prime_pow T (p := 2) (k := a) (by norm_num : Nat.Prime 2)
  by_cases hS2 : 2 ∈ S
  · have hT2 : 2 ∈ T := h2.mp hS2
    rw [hS, hT]
    simp [hS2, hT2]
  · have hT2 : 2 ∉ T := fun h => hS2 (h2.mpr h)
    rw [hS, hT]
    simp [hS2, hT2]

end Omega.Zeta
