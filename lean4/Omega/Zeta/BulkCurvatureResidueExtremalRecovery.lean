import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Filter
open scoped BigOperators Topology

noncomputable section

lemma xi_bulk_curvature_residue_extremal_recovery_tendsto_exp_neg {a : ℝ} (ha : a < 0) :
    Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * a)) atTop (𝓝 0) := by
  refine Real.tendsto_exp_atBot.comp ?_
  simpa [mul_comm] using tendsto_natCast_atTop_atTop.const_mul_atTop_of_neg ha

lemma xi_bulk_curvature_residue_extremal_recovery_normalized_identity {κ : ℕ}
    (σ : Fin κ → ℝ) (sigmaMax : ℝ) :
    (fun n : ℕ =>
        (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
          Real.exp (-(n : ℝ) * sigmaMax)) =
      fun n : ℕ => ∑ j : Fin κ, Real.exp ((n : ℝ) * (σ j - sigmaMax)) := by
  funext n
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl ?_
  intro j _hj
  rw [← Real.exp_add]
  congr 1
  ring

lemma xi_bulk_curvature_residue_extremal_recovery_count_sum {κ : ℕ}
    (σ : Fin κ → ℝ) (sigmaMax : ℝ) :
    (∑ j : Fin κ, if σ j = sigmaMax then (1 : ℝ) else 0) =
      ((Finset.univ.filter (fun j : Fin κ => σ j = sigmaMax)).card : ℝ) := by
  classical
  rw [← Finset.sum_filter]
  simp

lemma xi_bulk_curvature_residue_extremal_recovery_normalized_tendsto {κ : ℕ}
    (σ : Fin κ → ℝ) (sigmaMax : ℝ) (rMax : ℕ) (hle : ∀ j, σ j ≤ sigmaMax)
    (hrmax : (Finset.univ.filter (fun j : Fin κ => σ j = sigmaMax)).card = rMax) :
    Tendsto
      (fun n : ℕ =>
        (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
          Real.exp (-(n : ℝ) * sigmaMax))
      atTop (𝓝 (rMax : ℝ)) := by
  classical
  rw [xi_bulk_curvature_residue_extremal_recovery_normalized_identity σ sigmaMax]
  have hterms :
      ∀ j : Fin κ,
        Tendsto (fun n : ℕ => Real.exp ((n : ℝ) * (σ j - sigmaMax))) atTop
          (𝓝 (if σ j = sigmaMax then (1 : ℝ) else 0)) := by
    intro j
    by_cases hj : σ j = sigmaMax
    · simp [hj]
    · have hlt : σ j - sigmaMax < 0 := by
        have hstrict : σ j < sigmaMax := lt_of_le_of_ne (hle j) hj
        linarith
      simpa [hj] using
        xi_bulk_curvature_residue_extremal_recovery_tendsto_exp_neg hlt
  have hsum :
      Tendsto (fun n : ℕ => ∑ j : Fin κ, Real.exp ((n : ℝ) * (σ j - sigmaMax)))
        atTop (𝓝 (∑ j : Fin κ, if σ j = sigmaMax then (1 : ℝ) else 0)) := by
    simpa using tendsto_finset_sum Finset.univ (fun j _hj => hterms j)
  convert hsum using 1
  rw [xi_bulk_curvature_residue_extremal_recovery_count_sum σ sigmaMax, hrmax]

lemma xi_bulk_curvature_residue_extremal_recovery_rMax_pos {κ : ℕ} (σ : Fin κ → ℝ)
    (sigmaMax : ℝ) (rMax : ℕ) (hexists : ∃ j, σ j = sigmaMax)
    (hrmax : (Finset.univ.filter (fun j : Fin κ => σ j = sigmaMax)).card = rMax) :
    0 < rMax := by
  classical
  obtain ⟨j, hj⟩ := hexists
  rw [← hrmax]
  exact Finset.card_pos.mpr ⟨j, by simp [hj]⟩

lemma xi_bulk_curvature_residue_extremal_recovery_log_tendsto {κ : ℕ}
    (σ : Fin κ → ℝ) (sigmaMax : ℝ) (rMax : ℕ) (hle : ∀ j, σ j ≤ sigmaMax)
    (hexists : ∃ j, σ j = sigmaMax)
    (hrmax : (Finset.univ.filter (fun j : Fin κ => σ j = sigmaMax)).card = rMax) :
    Tendsto (fun n : ℕ =>
      (1 / (n : ℝ)) * Real.log (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)))
      atTop (𝓝 sigmaMax) := by
  classical
  have hnorm :=
    xi_bulk_curvature_residue_extremal_recovery_normalized_tendsto σ sigmaMax rMax hle hrmax
  have hrpos_nat :
      0 < rMax :=
    xi_bulk_curvature_residue_extremal_recovery_rMax_pos σ sigmaMax rMax hexists hrmax
  have hrpos : (0 : ℝ) < (rMax : ℝ) := by exact_mod_cast hrpos_nat
  have hlognorm :
      Tendsto
        (fun n : ℕ =>
          Real.log
            ((∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
              Real.exp (-(n : ℝ) * sigmaMax)))
        atTop (𝓝 (Real.log (rMax : ℝ))) :=
    (Real.continuousAt_log hrpos.ne').tendsto.comp hnorm
  have hinv : Tendsto (fun n : ℕ => (1 / (n : ℝ))) atTop (𝓝 0) := by
    simpa [one_div] using tendsto_natCast_atTop_atTop.inv_tendsto_atTop
  have hsmall :
      Tendsto
        (fun n : ℕ =>
          (1 / (n : ℝ)) *
            Real.log
              ((∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
                Real.exp (-(n : ℝ) * sigmaMax)))
        atTop (𝓝 0) := by
    simpa using hinv.mul hlognorm
  have hevent :
      ∀ᶠ n : ℕ in atTop,
        (1 / (n : ℝ)) * Real.log (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) =
          sigmaMax +
            (1 / (n : ℝ)) *
              Real.log
                ((∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
                  Real.exp (-(n : ℝ) * sigmaMax)) := by
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
    have hsum_pos : 0 < ∑ j : Fin κ, Real.exp ((n : ℝ) * σ j) := by
      obtain ⟨j, _hj⟩ := hexists
      exact Finset.sum_pos (fun j _ => Real.exp_pos _) ⟨j, Finset.mem_univ j⟩
    have hexp_pos : 0 < Real.exp (-(n : ℝ) * sigmaMax) := Real.exp_pos _
    rw [Real.log_mul hsum_pos.ne' hexp_pos.ne', Real.log_exp]
    field_simp [hnreal]
    ring
  have hmain :
      Tendsto
        (fun n : ℕ =>
          sigmaMax +
            (1 / (n : ℝ)) *
              Real.log
                ((∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) *
                  Real.exp (-(n : ℝ) * sigmaMax)))
        atTop (𝓝 sigmaMax) := by
    simpa using (tendsto_const_nhds.add hsmall)
  exact hmain.congr' (hevent.mono fun _n hn => hn.symm)

/-- Paper label: `cor:xi-bulk-curvature-residue-extremal-recovery`. -/
theorem paper_xi_bulk_curvature_residue_extremal_recovery {κ : ℕ} (_hκ : 0 < κ)
    (σ : Fin κ → ℝ) (sigmaMax : ℝ) (rMax : ℕ) (hle : ∀ j, σ j ≤ sigmaMax)
    (hexists : ∃ j, σ j = sigmaMax)
    (hrmax : (Finset.univ.filter (fun j : Fin κ => σ j = sigmaMax)).card = rMax) :
    Tendsto (fun n : ℕ =>
      (1 / (n : ℝ)) * Real.log (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)))
      atTop (𝓝 sigmaMax) ∧
      Tendsto (fun n : ℕ =>
        (∑ j : Fin κ, Real.exp ((n : ℝ) * σ j)) * Real.exp (-(n : ℝ) * sigmaMax))
        atTop (𝓝 (rMax : ℝ)) := by
  exact ⟨
    xi_bulk_curvature_residue_extremal_recovery_log_tendsto σ sigmaMax rMax hle hexists hrmax,
    xi_bulk_curvature_residue_extremal_recovery_normalized_tendsto σ sigmaMax rMax hle hrmax⟩

end

end Omega.Zeta
