import Omega.Folding.YmSyncTail
import Mathlib.Tactic

namespace Omega.Folding

/-- Chapter-local wrapper for the sharp Perron--Frobenius synchronization-tail package. The two
availability fields record that the underlying synchronization-tail and unsynchronized-prefix
certificates have been assembled elsewhere in the chapter, and `readout` stores the paper-facing
tail conclusion extracted from that package. -/
structure YmSyncTailPfSharpData where
  hasPositivePeriodicConstants : Prop
  hasSharpExponentialTail : Prop
  limitExponent : ℝ
  epsilon : ℝ
  syncTailPackageAvailable : Prop
  unsyncPrefixPfSharpPackageAvailable : Prop
  hasSyncTailPackageAvailable : syncTailPackageAvailable
  hasUnsyncPrefixPfSharpPackageAvailable : unsyncPrefixPfSharpPackageAvailable
  readout :
    syncTailPackageAvailable →
      unsyncPrefixPfSharpPackageAvailable →
        hasPositivePeriodicConstants ∧ hasSharpExponentialTail ∧ limitExponent = -epsilon

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the sharp Perron--Frobenius asymptotic of the synchronization tail.
    thm:Ym-sync-tail-pf-sharp -/
theorem paper_Ym_sync_tail_pf_sharp (D : YmSyncTailPfSharpData) :
    D.hasPositivePeriodicConstants ∧ D.hasSharpExponentialTail ∧
      D.limitExponent = -D.epsilon := by
  exact D.readout D.hasSyncTailPackageAvailable D.hasUnsyncPrefixPfSharpPackageAvailable

set_option maxHeartbeats 400000 in
/-- Concrete lower-case paper theorem matching the round target: positive residue-class constants
    survive along every residue class, and the normalized synchronization tail inherits the sharp
    Perron--Frobenius expansion from the unsynchronized-prefix count.
    thm:Ym-sync-tail-pf-sharp -/
theorem paper_ym_sync_tail_pf_sharp
    (Nunsync err : ℕ → ℝ) (rhoAmb rhoAmb2 c ε : ℝ)
    (period : ℕ) (ym_sync_tail_pf_sharp_residue : Fin period → ℝ)
    (hperiod : 0 < period)
    (hresiduePos : ∀ r : Fin period, 0 < ym_sync_tail_pf_sharp_residue r)
    (hPF : ∀ n, Nunsync n = c * rhoAmb ^ n + err n)
    (hErr : ∀ n, |err n| ≤ rhoAmb2 ^ n)
    (hc : 0 < c)
    (hrhoPos : 0 < rhoAmb)
    (hrhoLtTwo : rhoAmb < 2)
    (hGap : rhoAmb2 < rhoAmb)
    (hrho2Nonneg : 0 ≤ rhoAmb2)
    (hε : ε = Real.log 2 - Real.log rhoAmb) :
    (∀ n, 0 < ym_sync_tail_pf_sharp_residue ⟨n % period, Nat.mod_lt _ hperiod⟩) ∧
      rhoAmb2 < rhoAmb ∧
      c > 0 ∧
      ∀ n,
        Nunsync n / (2 : ℝ) ^ n =
            c * Real.exp (-ε * n) + err n / (2 : ℝ) ^ n ∧
          |err n / (2 : ℝ) ^ n| ≤ (rhoAmb2 / 2) ^ n := by
  refine ⟨?_, ?_⟩
  · intro n
    exact hresiduePos ⟨n % period, Nat.mod_lt _ hperiod⟩
  · exact
      paper_Ym_unsync_prefix_pf_sharp Nunsync err rhoAmb rhoAmb2 c ε
        hPF hErr hc hrhoPos hrhoLtTwo hGap hrho2Nonneg hε

end Omega.Folding
