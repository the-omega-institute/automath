import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `con:xi-grid-scan-two-step-dealiasing`. -/
theorem paper_xi_grid_scan_two_step_dealiasing {Delta DeltaPrime : ℝ} (hDelta : 0 < Delta)
    (hDeltaPrime : 0 < DeltaPrime) :
    (Irrational (Delta / DeltaPrime) →
      ∀ T : ℝ,
        (∃ m : ℤ, T = (2 * Real.pi * m) / Delta) →
          (∃ n : ℤ, T = (2 * Real.pi * n) / DeltaPrime) → T = 0) ∧
      (∀ p q : ℕ,
        0 < p →
          0 < q →
            Delta / DeltaPrime = (p : ℝ) / (q : ℝ) →
              ∃ d : ℝ, 0 < d ∧ Delta = (p : ℝ) * d ∧ DeltaPrime = (q : ℝ) * d) := by
  constructor
  · intro hIrr T hTDelta hTDeltaPrime
    rcases hTDelta with ⟨m, hm⟩
    rcases hTDeltaPrime with ⟨n, hn⟩
    by_contra hT_ne
    have hm_ne : m ≠ 0 := by
      intro hm0
      apply hT_ne
      simpa [hm0] using hm
    have hn_ne : n ≠ 0 := by
      intro hn0
      apply hT_ne
      simpa [hn0] using hn
    have htwo_pi_ne : (2 * Real.pi : ℝ) ≠ 0 := by
      exact mul_ne_zero two_ne_zero Real.pi_ne_zero
    have hnR_ne : (n : ℝ) ≠ 0 := by
      exact_mod_cast hn_ne
    have hgrid :
        (2 * Real.pi * (m : ℝ)) / Delta =
          (2 * Real.pi * (n : ℝ)) / DeltaPrime := by
      rw [← hm, hn]
    have hratio : Delta / DeltaPrime = (m : ℝ) / (n : ℝ) := by
      field_simp [hDelta.ne', hDeltaPrime.ne', htwo_pi_ne, hnR_ne] at hgrid ⊢
      nlinarith [hgrid]
    have hrat : Delta / DeltaPrime ∈ Set.range Rat.cast := by
      refine ⟨(m : ℚ) / (n : ℚ), ?_⟩
      simpa using hratio.symm
    exact hIrr hrat
  · intro p q hp hq hratio
    have hpR_pos : 0 < (p : ℝ) := by exact_mod_cast hp
    have hqR_pos : 0 < (q : ℝ) := by exact_mod_cast hq
    refine ⟨Delta / (p : ℝ), div_pos hDelta hpR_pos, ?_, ?_⟩
    · field_simp [hpR_pos.ne']
    · have hcross : (q : ℝ) * Delta = (p : ℝ) * DeltaPrime := by
        field_simp [hDeltaPrime.ne', hqR_pos.ne'] at hratio
        nlinarith [hratio]
      field_simp [hpR_pos.ne']
      nlinarith [hcross]

end Omega.Zeta
