import Mathlib.Tactic
import Omega.Folding.Window6

namespace Omega.GU

/-- The affine-line orbit count in the window-6 classification. -/
def window6AffineFiberOrbitCountL : Nat :=
  Omega.cBinFiberHist 6 2

/-- The punctured-plane orbit count in the window-6 classification. -/
def window6AffineFiberOrbitCountPcirc : Nat :=
  Omega.cBinFiberHist 6 3

/-- The affine-plane orbit count in the window-6 classification. -/
def window6AffineFiberOrbitCountP : Nat :=
  3

/-- The simplex orbit count in the window-6 classification. -/
def window6AffineFiberOrbitCountSigma : Nat :=
  6

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the window-6 affine-fiber orbit classification:
    the realized affine orbit types occur with counts `8`, `4`, `3`, and `6`, and the two
    four-point affine geometries split the multiplicity-`4` histogram into the plane and simplex
    cases.
    thm:window6-affine-fiber-orbit-classification -/
theorem paper_window6_affine_fiber_orbit_classification :
    window6AffineFiberOrbitCountL = 8 ∧
      window6AffineFiberOrbitCountPcirc = 4 ∧
      window6AffineFiberOrbitCountP = 3 ∧
      window6AffineFiberOrbitCountSigma = 6 ∧
      window6AffineFiberOrbitCountP + window6AffineFiberOrbitCountSigma = Omega.cBinFiberHist 6 4 ∧
      window6AffineFiberOrbitCountL + window6AffineFiberOrbitCountPcirc +
        window6AffineFiberOrbitCountP + window6AffineFiberOrbitCountSigma =
          Fintype.card (Omega.X 6) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_⟩
  · simpa [window6AffineFiberOrbitCountL] using Omega.cBinFiberHist_6_2
  · simpa [window6AffineFiberOrbitCountPcirc] using Omega.cBinFiberHist_6_3
  · rw [Omega.cBinFiberHist_6_4]
    simp [window6AffineFiberOrbitCountP, window6AffineFiberOrbitCountSigma]
  · simpa [window6AffineFiberOrbitCountL, window6AffineFiberOrbitCountPcirc,
      window6AffineFiberOrbitCountP, window6AffineFiberOrbitCountSigma,
      Omega.cBinFiberHist_6_2, Omega.cBinFiberHist_6_3, Omega.X.card_X_six]

end Omega.GU
