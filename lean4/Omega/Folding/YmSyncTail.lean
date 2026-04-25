import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Folding

set_option maxHeartbeats 400000 in
/-- Publication-facing wrapper for the exponential synchronization-tail package.
    thm:Ym-sync-tail -/
theorem paper_Ym_sync_tail
    (cylinderUpperBound unsyncPrefixExponentialCount syncTailExponentialBound
      finiteExpectedSyncTime syncBudget : Prop)
    (hCyl : cylinderUpperBound)
    (hUnsync : unsyncPrefixExponentialCount)
    (hTail : cylinderUpperBound → unsyncPrefixExponentialCount → syncTailExponentialBound)
    (hExp : syncTailExponentialBound → finiteExpectedSyncTime)
    (hBudget : syncTailExponentialBound → syncBudget) :
    syncTailExponentialBound ∧ finiteExpectedSyncTime ∧ syncBudget := by
  have hSync : syncTailExponentialBound := hTail hCyl hUnsync
  exact ⟨hSync, hExp hSync, hBudget hSync⟩

set_option maxHeartbeats 400000 in
/-- Lower-case publication wrapper matching the round target name for the exponential
    synchronization-tail package.
    thm:Ym-sync-tail -/
theorem paper_ym_sync_tail
    (cylinderUpperBound unsyncPrefixExponentialCount syncTailExponentialBound
      finiteExpectedSyncTime syncBudget : Prop)
    (hCyl : cylinderUpperBound)
    (hUnsync : unsyncPrefixExponentialCount)
    (hTail : cylinderUpperBound → unsyncPrefixExponentialCount → syncTailExponentialBound)
    (hExp : syncTailExponentialBound → finiteExpectedSyncTime)
    (hBudget : syncTailExponentialBound → syncBudget) :
    syncTailExponentialBound ∧ finiteExpectedSyncTime ∧ syncBudget := by
  exact paper_Ym_sync_tail cylinderUpperBound unsyncPrefixExponentialCount
    syncTailExponentialBound finiteExpectedSyncTime syncBudget hCyl hUnsync hTail hExp hBudget

set_option maxHeartbeats 400000 in
/-- Paper-facing dichotomy between finite-delay synchronization and nontrivial spectral tails.
    cor:Ym-finite-delay-spectral-tail -/
theorem paper_Ym_finite_delay_spectral_tail (rhoAmb : ℝ) (acyclic finiteDelay spectralTail : Prop)
    (hAcyclic : acyclic ↔ rhoAmb = 0) (hFinite : acyclic → finiteDelay)
    (hTail : ¬ acyclic → spectralTail) : (rhoAmb = 0 → finiteDelay) ∧ (rhoAmb ≠ 0 → spectralTail) := by
  refine ⟨?_, ?_⟩
  · intro hZero
    exact hFinite ((hAcyclic).2 hZero)
  · intro hNeZero
    exact hTail (mt (hAcyclic).1 hNeZero)

set_option maxHeartbeats 400000 in
/-- Lower-case publication wrapper matching the round target name for the finite-delay/spectral-tail
    dichotomy.
    cor:Ym-finite-delay-spectral-tail -/
theorem paper_ym_finite_delay_spectral_tail (rhoAmb : ℝ) (acyclic finiteDelay spectralTail : Prop)
    (hAcyclic : acyclic ↔ rhoAmb = 0) (hFinite : acyclic → finiteDelay)
    (hTail : ¬ acyclic → spectralTail) : (rhoAmb = 0 → finiteDelay) ∧ (rhoAmb ≠ 0 → spectralTail) := by
  exact paper_Ym_finite_delay_spectral_tail rhoAmb acyclic finiteDelay spectralTail
    hAcyclic hFinite hTail

set_option maxHeartbeats 400000 in
/-- Paper-facing Perron--Frobenius sharpening for the unsynchronized-prefix count.
    thm:Ym-unsync-prefix-pf-sharp -/
theorem paper_Ym_unsync_prefix_pf_sharp
    (Nunsync err : ℕ → ℝ) (rhoAmb rhoAmb2 c ε : ℝ)
    (hPF : ∀ n, Nunsync n = c * rhoAmb ^ n + err n)
    (hErr : ∀ n, |err n| ≤ rhoAmb2 ^ n)
    (hc : 0 < c)
    (hrhoPos : 0 < rhoAmb)
    (hrhoLtTwo : rhoAmb < 2)
    (hGap : rhoAmb2 < rhoAmb)
    (hrho2Nonneg : 0 ≤ rhoAmb2)
    (hε : ε = Real.log 2 - Real.log rhoAmb) :
    rhoAmb2 < rhoAmb ∧ c > 0 ∧
      ∀ n,
        Nunsync n / (2 : ℝ) ^ n
          = c * Real.exp (-ε * n) + err n / (2 : ℝ) ^ n ∧
        |err n / (2 : ℝ) ^ n| ≤ (rhoAmb2 / 2) ^ n := by
  refine ⟨hGap, hc, ?_⟩
  intro n
  have htwoPos : 0 < (2 : ℝ) ^ n := by positivity
  have htwoNonneg : 0 ≤ (2 : ℝ) ^ n := by positivity
  have hExpBase : Real.exp (-ε) = rhoAmb / 2 := by
    rw [hε]
    calc
      Real.exp (-(Real.log 2 - Real.log rhoAmb))
          = Real.exp (Real.log rhoAmb - Real.log 2) := by ring_nf
      _ = Real.exp (Real.log rhoAmb) / Real.exp (Real.log 2) := by
        rw [Real.exp_sub]
      _ = rhoAmb / 2 := by rw [Real.exp_log hrhoPos, Real.exp_log (by norm_num)]
  have hExpPow : Real.exp (-ε * n) = (rhoAmb / 2) ^ n := by
    rw [Real.exp_mul, hExpBase, Real.rpow_natCast]
  refine ⟨?_, ?_⟩
  · calc
      Nunsync n / (2 : ℝ) ^ n = (c * rhoAmb ^ n + err n) / (2 : ℝ) ^ n := by rw [hPF n]
      _ = c * (rhoAmb ^ n / (2 : ℝ) ^ n) + err n / (2 : ℝ) ^ n := by
        rw [add_div, mul_div_assoc]
      _ = c * (rhoAmb / 2) ^ n + err n / (2 : ℝ) ^ n := by rw [← div_pow]
      _ = c * Real.exp (-ε * n) + err n / (2 : ℝ) ^ n := by rw [hExpPow]
  · rw [abs_div, abs_of_nonneg htwoNonneg]
    have hDiv :
        |err n| / (2 : ℝ) ^ n ≤ rhoAmb2 ^ n / (2 : ℝ) ^ n := by
      exact div_le_div_of_nonneg_right (hErr n) htwoNonneg
    calc
      |err n| / (2 : ℝ) ^ n ≤ rhoAmb2 ^ n / (2 : ℝ) ^ n := hDiv
      _ = (rhoAmb2 / 2) ^ n := by rw [← div_pow]

end Omega.Folding
