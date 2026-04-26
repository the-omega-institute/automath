import Mathlib

namespace Omega.Zeta

noncomputable section

/-- The inverse spacing amplification for one grid-scan candidate. -/
def xiGridScanConditionNumber (target : ℝ) (a : ℚ) : ℝ :=
  1 / |target - (a : ℝ)|

/-- A Diophantine lower bound on near-period collisions along a scan family. -/
def xiGridScanDiophantineLowerBound
    (target : ℝ) (scan : ℕ → ℚ) (C : ℝ) (τ : ℕ) : Prop :=
  ∀ n : ℕ, C / ((n + 1 : ℝ) ^ τ) ≤ |target - (scan n : ℝ)|

/-- A Liouville sequence of rational approximants forcing exceptionally close collisions. -/
def xiGridScanLiouvilleSequence (target : ℝ) (scan : ℕ → ℚ) (τ : ℕ) : Prop :=
  ∀ K > 0, ∃ n : ℕ,
    0 < |target - (scan n : ℝ)| ∧
      |target - (scan n : ℝ)| < 1 / (K * ((n + 1 : ℝ) ^ τ))

private lemma xiGridScan_power_pos (n τ : ℕ) : 0 < ((n + 1 : ℝ) ^ τ) := by
  positivity

lemma xiGridScanConditionNumber_le_of_diophantine
    {target : ℝ} {scan : ℕ → ℚ} {C : ℝ} {τ n : ℕ}
    (hC : 0 < C) (hDioph : xiGridScanDiophantineLowerBound target scan C τ) :
    xiGridScanConditionNumber target (scan n) ≤ ((n + 1 : ℝ) ^ τ) / C := by
  let scale : ℝ := ((n + 1 : ℝ) ^ τ)
  let err : ℝ := |target - (scan n : ℝ)|
  have hscale : 0 < scale := by
    dsimp [scale]
    exact xiGridScan_power_pos n τ
  have hbound : C / scale ≤ err := by
    simpa [scale, err] using hDioph n
  have herr : 0 < err := lt_of_lt_of_le (div_pos hC hscale) hbound
  have hmul : C ≤ err * scale := by
    exact (div_le_iff₀ hscale).1 hbound
  have hdiv : C / err ≤ scale := by
    exact (div_le_iff₀ herr).2 (by simpa [mul_comm, mul_left_comm, mul_assoc] using hmul)
  have hmain : 1 / err ≤ scale / C := by
    exact (le_div_iff₀ hC).2 (by
      simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hdiv)
  simpa [xiGridScanConditionNumber, scale, err] using hmain

lemma xiGridScanConditionNumber_lt_of_liouville
    {target : ℝ} {scan : ℕ → ℚ} {τ n : ℕ} {K : ℝ}
    (hK : 0 < K)
    (hpos : 0 < |target - (scan n : ℝ)|)
    (hclose : |target - (scan n : ℝ)| < 1 / (K * ((n + 1 : ℝ) ^ τ))) :
    K * ((n + 1 : ℝ) ^ τ) < xiGridScanConditionNumber target (scan n) := by
  let scale : ℝ := ((n + 1 : ℝ) ^ τ)
  let err : ℝ := |target - (scan n : ℝ)|
  have hscale : 0 < scale := by
    dsimp [scale]
    exact xiGridScan_power_pos n τ
  have hks : 0 < K * scale := mul_pos hK hscale
  have hprod : err * (K * scale) < 1 := by
    exact (lt_div_iff₀ hks).1 (by simpa [err, scale] using hclose)
  have hmain : K * scale < 1 / err := by
    exact (lt_div_iff₀ hpos).2
      (by simpa [mul_comm, mul_left_comm, mul_assoc] using hprod)
  simpa [xiGridScanConditionNumber, scale, err] using hmain

/-- Paper label: `prop:xi-grid-scan-diophantine-dealiasing-stability`. A two-step grid scan is
polynomially stable under a uniform Diophantine separation estimate on both steps, while either
step carrying a Liouville chain of anomalously close rational approximants forces arbitrarily
large inverse-spacing amplification. -/
theorem paper_xi_grid_scan_diophantine_dealiasing_stability
    (target : ℝ) (scan₁ scan₂ : ℕ → ℚ) (C : ℝ) (τ : ℕ) (hC : 0 < C) :
    ((xiGridScanDiophantineLowerBound target scan₁ C τ ∧
        xiGridScanDiophantineLowerBound target scan₂ C τ) →
      ∀ n : ℕ, xiGridScanConditionNumber target (scan₁ n) ≤ ((n + 1 : ℝ) ^ τ) / C ∧
        xiGridScanConditionNumber target (scan₂ n) ≤ ((n + 1 : ℝ) ^ τ) / C) ∧
    ((xiGridScanLiouvilleSequence target scan₁ τ ∨
        xiGridScanLiouvilleSequence target scan₂ τ) →
      ∀ K > 0, ∃ n : ℕ,
        K * ((n + 1 : ℝ) ^ τ) < xiGridScanConditionNumber target (scan₁ n) ∨
          K * ((n + 1 : ℝ) ^ τ) < xiGridScanConditionNumber target (scan₂ n)) := by
  refine ⟨?_, ?_⟩
  · intro hDioph n
    exact ⟨xiGridScanConditionNumber_le_of_diophantine hC hDioph.1,
      xiGridScanConditionNumber_le_of_diophantine hC hDioph.2⟩
  · intro hLiouville K hK
    rcases hLiouville with h₁ | h₂
    · rcases h₁ K hK with ⟨n, hpos, hclose⟩
      exact ⟨n, Or.inl (xiGridScanConditionNumber_lt_of_liouville hK hpos hclose)⟩
    · rcases h₂ K hK with ⟨n, hpos, hclose⟩
      exact ⟨n, Or.inr (xiGridScanConditionNumber_lt_of_liouville hK hpos hclose)⟩

end

end Omega.Zeta
