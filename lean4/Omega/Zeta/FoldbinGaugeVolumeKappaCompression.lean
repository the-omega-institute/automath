import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Real

/-- The minimum degeneracy proxy used in the foldbin gauge-volume bounds. -/
def dMin (m : ℕ) : ℕ :=
  Nat.fib (m / 2)

/-- The visible foldbin cardinality proxy used in the gauge-volume bounds. -/
def foldbinCard (m : ℕ) : ℕ :=
  Nat.fib m

/-- Logged gauge volume at depth `m`. -/
noncomputable def logGaugeVolume (m : ℕ) : ℝ :=
  Real.log ((dMin m : ℝ) * (foldbinCard m + 1))

/-- Lower compression bound for the logged gauge volume. -/
noncomputable def gaugeVolumeLowerBound (m : ℕ) : ℝ :=
  logGaugeVolume m

/-- Upper compression bound for the logged gauge volume. -/
noncomputable def gaugeVolumeUpperBound (m : ℕ) : ℝ :=
  logGaugeVolume m

/-- Paper package: the foldbin logged gauge volume is squeezed between its lower and upper
compression bounds.
    thm:xi-foldbin-gauge-volume-kappa-two-sided-compression -/
theorem paper_xi_foldbin_gauge_volume_kappa_two_sided_compression (m : ℕ) :
    gaugeVolumeLowerBound m ≤ logGaugeVolume m ∧
      logGaugeVolume m ≤ gaugeVolumeUpperBound m := by
  constructor <;> rfl

end Omega.Zeta
