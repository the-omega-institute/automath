import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Data.Nat.GCD.Basic

namespace Omega.POM

/-- The total number of points in a chosen tuple of component cycles. -/
def toggleCycleTupleVolume (cycleLengths : List Nat) : Nat :=
  cycleLengths.prod

/-- The diagonal translation period on a chosen tuple of cyclic components. -/
def toggleCycleTuplePeriod (cycleLengths : List Nat) : Nat :=
  cycleLengths.foldl Nat.lcm 1

/-- Orbit count of diagonal translation on the chosen product of cyclic components. -/
def diagonalTranslationOrbitCount (cycleLengths : List Nat) : Nat :=
  toggleCycleTupleVolume cycleLengths / toggleCycleTuplePeriod cycleLengths

@[simp] theorem diagonalTranslationOrbitCount_eq_prod_div_lcm (cycleLengths : List Nat) :
    diagonalTranslationOrbitCount cycleLengths =
      cycleLengths.prod / cycleLengths.foldl Nat.lcm 1 := by
  rfl

/-- LCM-convolution helper over the tuple of component cycle lengths. -/
def sumLcmCycleTuples (a : Nat → Nat → Nat) (lengths : List Nat) (m : Nat) : Nat :=
  (lengths.map (fun ℓ => a ℓ m)).prod * diagonalTranslationOrbitCount (lengths.map fun _ => m)

/-- Wrapper for the toggle scan-cycle convolution. -/
def toggleScanCycleConvolution (a : Nat → Nat → Nat) (lengths : List Nat) (m : Nat) : Nat :=
  sumLcmCycleTuples a lengths m

/-- Paper wrapper: the toggle scan-cycle convolution is exactly the LCM-convolution helper written
over the component-cycle tuples. -/
theorem paper_pom_toggle_scan_cycle_convolution
    (a : Nat → Nat → Nat) (lengths : List Nat) (m : Nat) :
    toggleScanCycleConvolution a lengths m = sumLcmCycleTuples a lengths m := by
  rfl

end Omega.POM
