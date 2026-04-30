import Omega.Zeta.ResolutionRecursionZeroDrift

namespace Omega.Zeta

/-- Concrete adjacent-level truncation package.  The one-step Riemann--Siegel comparison is
represented by the already verified resolution-recursion datum, with the next truncation playing
the role of `Z^(m+1)`, the current truncation playing the role of `Z^m`, and the perturbation
envelope playing the role of the adjacent sup-norm error. -/
structure xi_riemann_siegel_adjacent_level_zero_homotopy_data where
  zeroDriftDatum : XiResolutionRecursionZeroDriftData

namespace xi_riemann_siegel_adjacent_level_zero_homotopy_data

/-- The adjacent Rouché--Taylor zero transfer specialized to the packaged truncation datum. -/
def zero_transfer (D : xi_riemann_siegel_adjacent_level_zero_homotopy_data) : Prop :=
  D.zeroDriftDatum.nextZeroExistsUnique

/-- The corresponding adjacent-level drift bound. -/
def drift_bound (D : xi_riemann_siegel_adjacent_level_zero_homotopy_data) : Prop :=
  D.zeroDriftDatum.nextZeroDriftBound

end xi_riemann_siegel_adjacent_level_zero_homotopy_data

/-- Paper label: `prop:xi-riemann-siegel-adjacent-level-zero-homotopy`. -/
theorem paper_xi_riemann_siegel_adjacent_level_zero_homotopy
    (D : xi_riemann_siegel_adjacent_level_zero_homotopy_data) :
    D.zero_transfer ∧ D.drift_bound := by
  have h := paper_xi_resolution_recursion_zero_drift D.zeroDriftDatum
  exact ⟨h.1, h.2.2⟩

end Omega.Zeta
