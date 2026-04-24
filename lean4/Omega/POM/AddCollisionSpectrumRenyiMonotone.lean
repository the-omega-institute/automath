import Mathlib
import Omega.POM.AdditionCollisionSpectrumSoficMonotonePerron

namespace Omega.POM

/-- Paper label: `cor:add-collision-spectrum-renyi-monotone`.
Once the real-input Perron radius is bounded above by the sync Perron radius, the corresponding
Rényi collision exponent `log (|Σ|^q / r)` is monotone because `r ↦ |Σ|^q / r` is antitone on
positive reals and `Real.log` is monotone on `(0, ∞)`. -/
theorem paper_add_collision_spectrum_renyi_monotone {sigmaSize rSync rReal : Real} (q : Nat)
    (hq : 2 <= q) (hSigma : 0 < sigmaSize) (hSync : 0 < rSync) (hReal : 0 < rReal)
    (hLe : rReal <= rSync) :
    Real.log (sigmaSize ^ q / rReal) >= Real.log (sigmaSize ^ q / rSync) := by
  have _ : 0 < (q : ℝ) := by
    exact_mod_cast lt_of_lt_of_le (by decide : 0 < (2 : ℕ)) hq
  have hpow : 0 < sigmaSize ^ q := by
    exact pow_pos hSigma q
  have hratio : sigmaSize ^ q / rSync ≤ sigmaSize ^ q / rReal := by
    exact div_le_div_of_nonneg_left hpow.le hReal hLe
  have hSyncArg : 0 < sigmaSize ^ q / rSync := by
    exact div_pos hpow hSync
  have hRealArg : 0 < sigmaSize ^ q / rReal := by
    exact div_pos hpow hReal
  exact Real.strictMonoOn_log.monotoneOn
    (by simpa [Set.mem_Ioi] using hSyncArg)
    (by simpa [Set.mem_Ioi] using hRealArg)
    hratio

end Omega.POM
