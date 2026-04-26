import Mathlib.Tactic
import Omega.Zeta.XiTimePart71ZeroCosetFiniteIntersectionPairwiseCompatibility

namespace Omega.Zeta

/-- The nonempty simplices for the zero-coset nerve/clique comparison are restricted to the odd
layer on which the finite-intersection theorem applies. The empty simplex is treated separately in
the two ambient finite families below. -/
def xi_time_part71_zero_coset_nerve_flag_admissible (M : Nat) (σ : Finset Nat) : Prop :=
  0 < M ∧ Even M ∧
    (∀ g ∈ σ, 0 < g) ∧
    (∀ g ∈ σ, Odd (g / listGcd σ.toList))

/-- Finite nerve model on the odd layer: a simplex is admitted when the common arithmetic
progression intersection model is nonempty. -/
noncomputable def xi_time_part71_zero_coset_nerve (M : Nat) (G : Finset Nat) : Finset (Finset Nat) := by
  classical
  exact G.powerset.filter fun σ =>
    σ = ∅ ∨
      (xi_time_part71_zero_coset_nerve_flag_admissible M σ ∧
        (zeroCosetIntersectionModel M σ.toList).Nonempty)

/-- Finite clique model on the same odd layer: a simplex is admitted when every pair is
arithmetically compatible. -/
noncomputable def xi_time_part71_zero_coset_clique_complex
    (M : Nat) (G : Finset Nat) : Finset (Finset Nat) := by
  classical
  exact G.powerset.filter fun σ =>
    σ = ∅ ∨
      (xi_time_part71_zero_coset_nerve_flag_admissible M σ ∧
        ∀ g₁ ∈ σ, ∀ g₂ ∈ σ, 2 * Nat.gcd g₁ g₂ ∣ g₂ - g₁)

/-- Paper label: `cor:xi-time-part71-zero-coset-nerve-flag`. On the odd layer where
`paper_xi_time_part71_zero_coset_finite_intersection_pairwise_compatibility` applies, the finite
zero-coset nerve agrees with the finite compatibility clique complex. -/
theorem paper_xi_time_part71_zero_coset_nerve_flag
    (M : Nat) (G : Finset Nat) (hG : ∀ g ∈ G, g ∣ M / 2) :
    xi_time_part71_zero_coset_nerve M G = xi_time_part71_zero_coset_clique_complex M G := by
  classical
  ext σ
  constructor
  · intro hσ
    simp [xi_time_part71_zero_coset_nerve, xi_time_part71_zero_coset_clique_complex] at hσ ⊢
    rcases hσ with ⟨hσG, hσ⟩
    by_cases hEmpty : σ = ∅
    · exact ⟨hσG, by simp [hEmpty]⟩
    · have hσne : σ ≠ ∅ := hEmpty
      have hmain :
          xi_time_part71_zero_coset_nerve_flag_admissible M σ ∧
            (zeroCosetIntersectionModel M σ.toList).Nonempty := by
        simpa [hσne] using hσ
      rcases hmain with ⟨hAdm, _⟩
      rcases hAdm with ⟨hM, hEven, hPos, hOdd⟩
      have hdiv :
          ∀ g ∈ σ.toList, 0 < g ∧ g ∣ M / 2 := by
        intro g hg
        refine ⟨hPos g (by simpa using hg), ?_⟩
        exact hG g (hσG (by simpa using hg))
      have hodd :
          ∀ g ∈ σ.toList, Odd (g / listGcd σ.toList) := by
        intro g hg
        exact hOdd g (by simpa using hg)
      have hpair :=
        (paper_xi_time_part71_zero_coset_finite_intersection_pairwise_compatibility
          M σ.toList (by simpa using hσne) hM hEven hdiv hodd).1
      refine ⟨hσG, ?_⟩
      right
      refine ⟨⟨hM, hEven, hPos, hOdd⟩, ?_⟩
      intro g₁ hg₁ g₂ hg₂
      exact hpair g₁ (by simpa using hg₁) g₂ (by simpa using hg₂)
  · intro hσ
    simp [xi_time_part71_zero_coset_nerve, xi_time_part71_zero_coset_clique_complex] at hσ ⊢
    rcases hσ with ⟨hσG, hσ⟩
    by_cases hEmpty : σ = ∅
    · exact ⟨hσG, by simp [hEmpty]⟩
    · have hσne : σ ≠ ∅ := hEmpty
      have hmain :
          xi_time_part71_zero_coset_nerve_flag_admissible M σ ∧
            (∀ g₁ ∈ σ, ∀ g₂ ∈ σ, 2 * Nat.gcd g₁ g₂ ∣ g₂ - g₁) := by
        simpa [hσne] using hσ
      rcases hmain with ⟨hAdm, hPair⟩
      rcases hAdm with ⟨hM, hEven, hPos, hOdd⟩
      have hdiv :
          ∀ g ∈ σ.toList, 0 < g ∧ g ∣ M / 2 := by
        intro g hg
        refine ⟨hPos g (by simpa using hg), ?_⟩
        exact hG g (hσG (by simpa using hg))
      have hodd :
          ∀ g ∈ σ.toList, Odd (g / listGcd σ.toList) := by
        intro g hg
        exact hOdd g (by simpa using hg)
      have hcompat :=
        paper_xi_time_part71_zero_coset_finite_intersection_pairwise_compatibility
          M σ.toList (by simpa using hσne) hM hEven hdiv hodd
      have hcard :
          (zeroCosetIntersectionModel M σ.toList).card = listGcd σ.toList := hcompat.2
      have hgcdpos : 0 < listGcd σ.toList := by
        exact listGcd_pos_of_nonempty (by simpa using hσne) (fun g hg => hPos g (by simpa using hg))
      have hnonempty : (zeroCosetIntersectionModel M σ.toList).Nonempty := by
        exact Finset.card_pos.mp (by simpa [hcard] using hgcdpos)
      refine ⟨hσG, ?_⟩
      right
      exact ⟨⟨hM, hEven, hPos, hOdd⟩, hnonempty⟩

end Omega.Zeta
