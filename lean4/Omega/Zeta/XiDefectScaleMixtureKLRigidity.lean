import Omega.Zeta.XiDefectScaleMixtureKLLeading

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- Paper label: `cor:xi-defect-scale-mixture-kl-rigidity`. In the concrete scale-mixture KL
model, a normalized limit of zero forces the leading quadratic coefficient to vanish, and
positivity of the weights then forces every nonnegative defect to be zero. -/
theorem paper_xi_defect_scale_mixture_kl_rigidity {N : ℕ} (δ m : Fin N → ℝ)
    (hδ_nonneg : ∀ j, 0 ≤ δ j) (hm_pos : ∀ j, 0 < m j)
    (hΦ : 0 < ∑ j, m j * δ j)
    (hsmall :
      Filter.Tendsto (fun t : ℝ => (t + 1)^2 * xiDefectScaleMixtureKL δ m t) Filter.atTop
        (𝓝 0)) :
    (∑ j, m j * (δ j)^2 = 0) ∧ ∀ j, δ j = 0 := by
  let S1 : ℝ := ∑ j, m j * δ j
  let S2 : ℝ := ∑ j, m j * (δ j) ^ (2 : ℕ)
  have hlead :
      Filter.Tendsto (fun t : ℝ => (t + 1)^2 * xiDefectScaleMixtureKL δ m t) Filter.atTop
        (𝓝 (((S2 / S1) ^ (2 : ℕ)) / 4)) := by
    simpa [S1, S2] using paper_xi_defect_scale_mixture_kl_leading δ m hδ_nonneg hm_pos hΦ
  have hconst_zero : ((S2 / S1) ^ (2 : ℕ)) / 4 = 0 := by
    exact tendsto_nhds_unique hlead hsmall
  have hratio_zero : S2 / S1 = 0 := by
    nlinarith [sq_nonneg (S2 / S1)]
  have hS1_ne : S1 ≠ 0 := by
    exact ne_of_gt (by simpa [S1] using hΦ)
  have hS2_zero : S2 = 0 := by
    calc
      S2 = (S2 / S1) * S1 := by field_simp [hS1_ne]
      _ = 0 := by rw [hratio_zero]; ring
  have hsum_zero : ∑ j, m j * (δ j) ^ (2 : ℕ) = 0 := by
    simpa [S2] using hS2_zero
  refine ⟨by simpa using hsum_zero, ?_⟩
  intro j
  have hterm_nonneg : ∀ k : Fin N, 0 ≤ m k * (δ k) ^ (2 : ℕ) := by
    intro k
    exact mul_nonneg (le_of_lt (hm_pos k)) (sq_nonneg (δ k))
  have hterm_zero : m j * (δ j) ^ (2 : ℕ) = 0 := by
    have hle :
        m j * (δ j) ^ (2 : ℕ) ≤ ∑ k : Fin N, m k * (δ k) ^ (2 : ℕ) :=
      Finset.single_le_sum (fun k _ => hterm_nonneg k) (Finset.mem_univ j)
    rw [hsum_zero] at hle
    exact le_antisymm hle (hterm_nonneg j)
  have hsquare_zero : (δ j) ^ (2 : ℕ) = 0 := by
    rcases mul_eq_zero.mp hterm_zero with hm_zero | hδ_zero
    · exact False.elim ((ne_of_gt (hm_pos j)) hm_zero)
    · exact hδ_zero
  exact sq_eq_zero_iff.mp hsquare_zero

end

end Omega.Zeta
