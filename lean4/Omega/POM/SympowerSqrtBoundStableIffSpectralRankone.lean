import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Tactic
import Omega.POM.SympowerSqrtBoundInstability

namespace Omega.POM

/-- Paper label: `cor:pom-sympower-sqrt-bound-stable-iff-spectral-rankone`. -/
theorem paper_pom_sympower_sqrt_bound_stable_iff_spectral_rankone (ρ μ : ℝ)
    (hρ : 1 < ρ) :
    ((∀ b : ℕ, 2 ≤ b →
      |pom_sympower_sqrt_bound_instability_candidate ρ μ b| ≤
        pom_sympower_sqrt_bound_instability_sqrt_barrier ρ b) ↔ μ = 0) := by
  constructor
  · intro hstable
    by_contra hμ
    have hρpos : 0 < ρ := lt_trans zero_lt_one hρ
    have hμpos : 0 < |μ| := abs_pos.mpr hμ
    have hpow_atTop : Filter.Tendsto (fun n : ℕ => ρ ^ n) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt hρ
    have hlarge_eventually : ∀ᶠ n : ℕ in Filter.atTop, 1 / |μ| < ρ ^ n :=
      hpow_atTop.eventually (Filter.eventually_gt_atTop (1 / |μ|))
    obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp hlarge_eventually
    have hpow_large : 1 / |μ| < ρ ^ n := hn n le_rfl
    have hscaled_large : 1 < ρ ^ n * |μ| := by
      have hmul := mul_lt_mul_of_pos_right hpow_large hμpos
      simpa [one_div, hμpos.ne'] using hmul
    let b : ℕ := 2 * n + 2
    have hb : 2 ≤ b := by
      dsimp [b]
      omega
    have hdiv : b / 2 = n + 1 := by
      dsimp [b]
      omega
    have hsub : b - 1 = 2 * n + 1 := by
      omega
    have hpow_nonneg : 0 ≤ ρ ^ (2 * n + 1) := le_of_lt (pow_pos hρpos _)
    have hbar_pos : 0 < ρ ^ (n + 1) := pow_pos hρpos _
    have hviolate :
        pom_sympower_sqrt_bound_instability_sqrt_barrier ρ b <
          |pom_sympower_sqrt_bound_instability_candidate ρ μ b| := by
      have hmul :
          ρ ^ (n + 1) < ρ ^ (n + 1) * (ρ ^ n * |μ|) := by
        simpa using mul_lt_mul_of_pos_left hscaled_large hbar_pos
      have hpow_factor : ρ ^ (n + 1) * (ρ ^ n * |μ|) = ρ ^ (2 * n + 1) * |μ| := by
        rw [← mul_assoc, ← pow_add]
        have hadd : n + 1 + n = 2 * n + 1 := by
          omega
        rw [hadd]
      calc
        pom_sympower_sqrt_bound_instability_sqrt_barrier ρ b = ρ ^ (n + 1) := by
          simp [pom_sympower_sqrt_bound_instability_sqrt_barrier, hdiv]
        _ < ρ ^ (2 * n + 1) * |μ| := hmul.trans_eq hpow_factor
        _ = |pom_sympower_sqrt_bound_instability_candidate ρ μ b| := by
          simp [pom_sympower_sqrt_bound_instability_candidate, hsub, abs_mul,
            abs_of_nonneg hpow_nonneg]
    exact not_lt_of_ge (hstable b hb) hviolate
  · intro hμ b _hb
    have hρnonneg : 0 ≤ ρ := le_of_lt (lt_trans zero_lt_one hρ)
    simp [pom_sympower_sqrt_bound_instability_candidate,
      pom_sympower_sqrt_bound_instability_sqrt_barrier, hμ, pow_nonneg hρnonneg]

end Omega.POM
