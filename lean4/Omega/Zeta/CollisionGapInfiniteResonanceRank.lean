import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part75a-collision-gap-infinite-resonance-rank`. -/
theorem paper_xi_time_part75a_collision_gap_infinite_resonance_rank
    (Gamma Cphi : ℕ → ℝ)
    (h_resonance_diverges :
      ∀ U : ℕ, ∀ M : ℝ,
        ∃ V : ℕ, U < V ∧ M < 2 * ∑ u ∈ Finset.Icc (U + 1) V, Cphi u ^ 2)
    (h_liminf_lower :
      ∀ V : ℕ, ∀ M : ℝ,
        M < 2 * ∑ u ∈ Finset.Icc 1 V, Cphi u ^ 2 →
          ∃ N : ℕ, ∀ m ≥ N, M ≤ Gamma m) :
    ∀ U : ℕ, ∀ M : ℝ,
      ∃ N : ℕ, ∀ m ≥ N,
        M ≤ Gamma m - 2 * ∑ u ∈ Finset.Icc 1 U, Cphi u ^ 2 := by
  intro U M
  let R : ℝ := 2 * ∑ u ∈ Finset.Icc 1 U, Cphi u ^ 2
  rcases h_resonance_diverges U (M + R) with ⟨V, _hUV, htail⟩
  have htail_le_full :
      2 * ∑ u ∈ Finset.Icc (U + 1) V, Cphi u ^ 2 ≤
        2 * ∑ u ∈ Finset.Icc 1 V, Cphi u ^ 2 := by
    have hsubset : Finset.Icc (U + 1) V ⊆ Finset.Icc 1 V := by
      intro u hu
      rw [Finset.mem_Icc] at hu ⊢
      omega
    have hsum_le :
        ∑ u ∈ Finset.Icc (U + 1) V, Cphi u ^ 2 ≤
          ∑ u ∈ Finset.Icc 1 V, Cphi u ^ 2 := by
      exact Finset.sum_le_sum_of_subset_of_nonneg hsubset (by
        intro u _hu_full _hu_tail
        exact sq_nonneg (Cphi u))
    linarith
  have hfull : M + R < 2 * ∑ u ∈ Finset.Icc 1 V, Cphi u ^ 2 :=
    lt_of_lt_of_le htail htail_le_full
  rcases h_liminf_lower V (M + R) hfull with ⟨N, hN⟩
  refine ⟨N, ?_⟩
  intro m hm
  have hGamma : M + R ≤ Gamma m := hN m hm
  dsimp [R] at hGamma ⊢
  linarith

end Omega.Zeta
