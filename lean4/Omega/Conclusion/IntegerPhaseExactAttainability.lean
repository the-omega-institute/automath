import Mathlib.Tactic

namespace Omega.Conclusion

/-- On the finite integer grid `1, ..., Q - 1`, discrete maximizers of the affine-tilted profile
are exactly the points satisfying the supporting-line inequalities; if the maximizer is interior,
the adjacent-node tests force the slope into the neighboring-difference interval.
    thm:conclusion-integer-phase-exact-attainability -/
theorem paper_conclusion_integer_phase_exact_attainability (Q n : ℕ) (hQ : 2 ≤ Q)
    (hn1 : 1 ≤ n) (hnQ : n < Q) (γ : ℝ) (Λ : ℕ → ℝ) :
    let admissible := Finset.Icc 1 (Q - 1)
    let isDiscreteMaximizer :=
      ∀ t ∈ admissible, (t : ℝ) * γ - Λ t ≤ (n : ℝ) * γ - Λ n
    let isSubgradient :=
      ∀ t ∈ admissible, Λ t ≥ Λ n + γ * ((t : ℝ) - n)
    isDiscreteMaximizer ↔
      (isSubgradient ∧
        ((1 < n ∧ n + 1 < Q) →
          γ ∈ Set.Icc (Λ n - Λ (n - 1)) (Λ (n + 1) - Λ n))) := by
  dsimp
  have hnQ_le : n ≤ Q - 1 := by omega
  constructor
  · intro hmax
    have hsub : ∀ t ∈ Finset.Icc 1 (Q - 1), Λ t ≥ Λ n + γ * ((t : ℝ) - n) := by
      intro t ht
      have h := hmax t ht
      linarith
    refine ⟨hsub, ?_⟩
    intro hinterior
    rcases hinterior with ⟨hn_lt, hn_succQ⟩
    have hnm1_mem : n - 1 ∈ Finset.Icc 1 (Q - 1) := by
      simp [Finset.mem_Icc]
      omega
    have hnp1_mem : n + 1 ∈ Finset.Icc 1 (Q - 1) := by
      simp [Finset.mem_Icc]
      omega
    have hleft : Λ (n - 1) ≥ Λ n + γ * (((n - 1 : ℕ) : ℝ) - n) := hsub (n - 1) hnm1_mem
    have hright : Λ (n + 1) ≥ Λ n + γ * (((n + 1 : ℕ) : ℝ) - n) := hsub (n + 1) hnp1_mem
    have hleft' : Λ (n - 1) ≥ Λ n - γ := by
      rw [Nat.cast_sub hn1] at hleft
      norm_num at hleft ⊢
      linarith
    have hright' : Λ (n + 1) ≥ Λ n + γ := by
      norm_num at hright ⊢
      linarith
    refine ⟨?_, ?_⟩
    · linarith
    · linarith
  · rintro ⟨hsub, _⟩
    intro t ht
    have h := hsub t ht
    linarith

end Omega.Conclusion
