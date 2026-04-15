import Mathlib.Tactic

namespace Omega.Folding.LocalRewriteLdpBarrier

noncomputable section

open scoped BigOperators

/-- Average deletion per local rewrite step. -/
def averageDeletion {T : ℕ} (Δ : Fin T → ℝ) : ℝ :=
  (∑ i, Δ i) / T

/-- Density of steps whose deletion is at most `R - ε`. -/
def lowDeletionDensity {T : ℕ} (Δ : Fin T → ℝ) (R ε : ℝ) : ℝ :=
  ((Finset.filter (fun i => Δ i ≤ R - ε) Finset.univ).card : ℝ) / T

/-- The telescoping identity `∑ Δ = G` turns the average deletion into `G / T`. -/
theorem averageDeletion_eq_total {T : ℕ} (Δ : Fin T → ℝ) (G : ℝ)
    (hG : (∑ i, Δ i) = G) :
    averageDeletion Δ = G / T := by
  simp [averageDeletion, hG]

/-- If every step deletes at most `R`, then the average is penalized by any positive density
    of steps that delete at most `R - ε`. -/
theorem averageDeletion_le_of_lowDeletionDensity
    {R ε : ℝ} {T : ℕ} (hT : 0 < T) (Δ : Fin T → ℝ)
    (hBound : ∀ i, Δ i ≤ R) :
    averageDeletion Δ ≤ R - ε * lowDeletionDensity Δ R ε := by
  have hsum :
      ∑ i, Δ i ≤
        ∑ i : Fin T, (R - ε * (if Δ i ≤ R - ε then (1 : ℝ) else 0)) := by
    refine Finset.sum_le_sum ?_
    intro i _
    by_cases hbad : Δ i ≤ R - ε
    · simp [hbad]
    · simp [hbad]
      exact hBound i
  have hcard :
      (∑ i : Fin T, if Δ i ≤ R - ε then (1 : ℝ) else 0) =
        ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ) := by
    simp
  have hT' : (0 : ℝ) < T := by
    exact_mod_cast hT
  have hdiv :
      averageDeletion Δ ≤
        (((T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ)) /
          T) := by
    unfold averageDeletion
    refine div_le_div_of_nonneg_right ?_ (le_of_lt hT')
    calc
      ∑ i, Δ i ≤
          ∑ i : Fin T, (R - ε * (if Δ i ≤ R - ε then (1 : ℝ) else 0)) := hsum
      _ = (T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ) := by
          rw [Finset.sum_sub_distrib]
          simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          rw [← Finset.mul_sum]
          simp [hcard]
  have hneT : (T : ℝ) ≠ 0 := by
    positivity
  calc
    averageDeletion Δ ≤
        (((T : ℝ) * R -
            ε * ((Finset.filter (fun i : Fin T => Δ i ≤ R - ε) Finset.univ).card : ℝ)) /
          T) := hdiv
    _ = R - ε * lowDeletionDensity Δ R ε := by
      unfold lowDeletionDensity
      field_simp [hneT]

/-- Exact saturation of the average forces the low-efficiency steps to have zero density. -/
theorem lowDeletionDensity_eq_zero_of_averageDeletion_eq_max
    {R ε : ℝ} {T : ℕ} (hT : 0 < T) (hε : 0 < ε) (Δ : Fin T → ℝ)
    (hBound : ∀ i, Δ i ≤ R)
    (hAvg : averageDeletion Δ = R) :
    lowDeletionDensity Δ R ε = 0 := by
  have hineq := averageDeletion_le_of_lowDeletionDensity (R := R) (ε := ε) hT Δ hBound
  rw [hAvg] at hineq
  have hnonneg : 0 ≤ lowDeletionDensity Δ R ε := by
    unfold lowDeletionDensity
    positivity
  nlinarith

/-- Paper-facing rigidity package: the sum identity gives the average deletion, and exact
    saturation rules out a positive density of suboptimal steps. -/
theorem paper_fold_local_rewrite_saturation_step_efficiency_rigidity :
    (∀ {T : ℕ} (Δ : Fin T → ℝ) (G : ℝ),
      (∑ i, Δ i) = G → averageDeletion Δ = G / T) ∧
    (∀ {R ε : ℝ} {T : ℕ}, 0 < T → 0 < ε →
      ∀ Δ : Fin T → ℝ,
      (∀ i, Δ i ≤ R) →
      averageDeletion Δ = R →
      lowDeletionDensity Δ R ε = 0) := by
  refine ⟨?_, ?_⟩
  · intro T Δ G hG
    exact averageDeletion_eq_total Δ G hG
  · intro R ε T hT hε Δ hBound hAvg
    exact lowDeletionDensity_eq_zero_of_averageDeletion_eq_max hT hε Δ hBound hAvg

end

end Omega.Folding.LocalRewriteLdpBarrier
