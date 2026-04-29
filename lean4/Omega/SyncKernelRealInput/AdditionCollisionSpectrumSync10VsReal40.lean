import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.SyncKernelRealInput

/-- Audited `q = 2` Perron-root proxy for the `10`-state sync kernel, recorded with the decimal
expansion used in the appendix table. -/
def addition_collision_spectrum_sync10_vs_real40_sync10_r2 : ℚ :=
  8743051527020 / 1000000000000

/-- Audited `q = 3` Perron-root proxy for the `10`-state sync kernel. -/
def addition_collision_spectrum_sync10_vs_real40_sync10_r3 : ℚ :=
  19850893522098 / 1000000000000

/-- Audited `q = 2` Perron-root proxy for the real-input `40`-state kernel. -/
def addition_collision_spectrum_sync10_vs_real40_real40_r2 : ℚ :=
  3998543344507 / 1000000000000

/-- Exact ratio of the two audited `q = 2` proxies. -/
def addition_collision_spectrum_sync10_vs_real40_ratio : ℚ :=
  addition_collision_spectrum_sync10_vs_real40_sync10_r2 /
    addition_collision_spectrum_sync10_vs_real40_real40_r2

/-- Paper label: `prop:addition-collision-spectrum-sync10-vs-real40`. -/
theorem paper_addition_collision_spectrum_sync10_vs_real40 :
    addition_collision_spectrum_sync10_vs_real40_sync10_r2 =
        8743051527020 / 1000000000000 ∧
      addition_collision_spectrum_sync10_vs_real40_sync10_r3 =
        19850893522098 / 1000000000000 ∧
      addition_collision_spectrum_sync10_vs_real40_real40_r2 =
        3998543344507 / 1000000000000 ∧
      addition_collision_spectrum_sync10_vs_real40_ratio =
        8743051527020 / 3998543344507 := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  norm_num [addition_collision_spectrum_sync10_vs_real40_ratio,
    addition_collision_spectrum_sync10_vs_real40_sync10_r2,
    addition_collision_spectrum_sync10_vs_real40_real40_r2]

end Omega.SyncKernelRealInput
