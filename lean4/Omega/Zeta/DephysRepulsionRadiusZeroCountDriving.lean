import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `cor:dephys-repulsion-radius-zero-count-driving`. -/
theorem paper_dephys_repulsion_radius_zero_count_driving
    (D logR N : ℝ → ℝ) (t : ℝ) (hD : HasDerivAt D (N t) t)
    (hlogR : ∀ s, logR s = s - D s) : HasDerivAt logR (1 - N t) t := by
  have hbase : HasDerivAt (fun s : ℝ => s - D s) (1 - N t) t := by
    simpa using (hasDerivAt_id t).sub hD
  have hfun : logR = fun s : ℝ => s - D s := funext hlogR
  simpa [hfun] using hbase

end Omega.Zeta
