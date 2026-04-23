import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete chapter-local data for a finite Mellin superposition restricted to a vertical line.
The restriction is sampled on a discrete period lattice: after a positive imaginary step `period`
the value repeats, while beyond the index `vanishingIndex` the restriction already vanishes. -/
structure XiScaleMellinNoNonzeroImagPeriodData where
  period : ℕ
  hperiod : 0 < period
  vanishingIndex : ℕ
  verticalRestriction : ℕ → ℂ
  hperiodic : ∀ n, verticalRestriction (n + period) = verticalRestriction n
  hvanishes : ∀ n, vanishingIndex ≤ n → verticalRestriction n = 0

namespace XiScaleMellinNoNonzeroImagPeriodData

/-- A nonzero imaginary period can only occur when the vertical restriction vanishes identically.
-/
def zeroIsOnlyImaginaryPeriod (data : XiScaleMellinNoNonzeroImagPeriodData) : Prop :=
  ∀ n : ℕ, data.verticalRestriction n = 0

end XiScaleMellinNoNonzeroImagPeriodData

private lemma xi_scale_mellin_no_nonzero_imag_period_shift
    (data : XiScaleMellinNoNonzeroImagPeriodData) (n k : ℕ) :
    data.verticalRestriction (n + k * data.period) = data.verticalRestriction n := by
  induction k with
  | zero =>
      simp
  | succ k ih =>
      calc
        data.verticalRestriction (n + Nat.succ k * data.period)
            = data.verticalRestriction ((n + k * data.period) + data.period) := by
                simp [Nat.succ_mul, Nat.add_left_comm, Nat.add_comm]
        _ = data.verticalRestriction (n + k * data.period) := data.hperiodic (n + k * data.period)
        _ = data.verticalRestriction n := ih

/-- Paper label: `prop:xi-scale-mellin-no-nonzero-imag-period`. Once a vertical restriction is
periodic with positive period and already vanishes sufficiently far out on the imaginary axis, the
periodicity propagates that vanishing back to every sampled height. -/
theorem paper_xi_scale_mellin_no_nonzero_imag_period
    (data : XiScaleMellinNoNonzeroImagPeriodData) : data.zeroIsOnlyImaginaryPeriod := by
  intro n
  let k := data.vanishingIndex + 1
  have hshift :
      data.verticalRestriction (n + k * data.period) = data.verticalRestriction n :=
    xi_scale_mellin_no_nonzero_imag_period_shift data n k
  have hlarge : data.vanishingIndex ≤ n + k * data.period := by
    have hkvanish : data.vanishingIndex ≤ k := by
      dsimp [k]
      omega
    have hkmul : k ≤ k * data.period := by
      exact Nat.le_mul_of_pos_right k data.hperiod
    exact le_trans hkvanish (le_trans hkmul (Nat.le_add_left _ _))
  have hzero : data.verticalRestriction (n + k * data.period) = 0 := data.hvanishes _ hlarge
  rw [hshift] at hzero
  exact hzero

end Omega.Zeta
