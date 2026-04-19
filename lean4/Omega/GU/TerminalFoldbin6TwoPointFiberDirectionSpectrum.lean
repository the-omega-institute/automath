import Mathlib.Tactic
import Omega.Folding.BinFold

namespace Omega.GU

structure TerminalFoldbin6TwoPointFiberDatum where
  fiberValue : Nat
  leftPreimage : Nat
  rightPreimage : Nat
  direction : Nat
  geoLeftImage : Nat
  geoRightImage : Nat
  deriving DecidableEq

/-- The ordered preimages of a window-6 BinFold fiber. -/
def terminalFoldbin6FiberPreimages (w : X 6) : List Nat :=
  ((Finset.range 64).filter fun n => cBinFold 6 n = w).sort (· ≤ ·)

/-- The geometric involution on 6-bit words, transported back to the integer encoding. -/
def terminalFoldbin6GeoImage (n : Nat) : Nat :=
  Int.toNat (binaryEncode6 (geoStabilizerAction (intToWord 6 n)))

/-- Explicit data for the eight size-2 fibers of `cBinFold` at window 6. -/
def terminalFoldbin6TwoPointFiberData : List TerminalFoldbin6TwoPointFiberDatum :=
  (List.range (Nat.fib 8)).filterMap fun n =>
    let ps := terminalFoldbin6FiberPreimages (X.ofNat 6 n)
    if ps.length = 2 then
      some
        { fiberValue := n
          leftPreimage := ps[0]!
          rightPreimage := ps[1]!
          direction := ps[0]! ^^^ ps[1]!
          geoLeftImage := terminalFoldbin6GeoImage ps[0]!
          geoRightImage := terminalFoldbin6GeoImage ps[1]! }
    else
      none

/-- The distinct XOR directions arising from the size-2 fibers. -/
def terminalFoldbin6TwoPointFiberDirectionSpectrum : Finset Nat :=
  (terminalFoldbin6TwoPointFiberData.map TerminalFoldbin6TwoPointFiberDatum.direction).toFinset

/-- The stable values of the size-2 fibers having a prescribed XOR direction. -/
def terminalFoldbin6FiberValuesByDirection (δ : Nat) : List Nat :=
  terminalFoldbin6TwoPointFiberData.filterMap fun d =>
    if d.direction = δ then some d.fiberValue else none

/-- The stable values of the size-2 fibers on which the geometric involution swaps the two
endpoints. -/
def terminalFoldbin6GeoSwapFiberValues : List Nat :=
  terminalFoldbin6TwoPointFiberData.filterMap fun d =>
    if d.geoLeftImage = d.rightPreimage ∧ d.geoRightImage = d.leftPreimage then
      some d.fiberValue
    else
      none

/-- Paper-facing classification of the window-6 size-2 BinFold fibers: their explicit
preimages, the resulting three-valued XOR direction spectrum, and the geometric criterion that
selects exactly the `34 = 100010₂` direction class.
    thm:terminal-foldbin6-two-point-fiber-direction-spectrum -/
theorem paper_terminal_foldbin6_two_point_fiber_direction_spectrum :
    terminalFoldbin6TwoPointFiberData =
      [ { fiberValue := 13, leftPreimage := 13, rightPreimage := 47, direction := 34,
          geoLeftImage := 47, geoRightImage := 13 }
      , { fiberValue := 14, leftPreimage := 14, rightPreimage := 48, direction := 62,
          geoLeftImage := 14, geoRightImage := 48 }
      , { fiberValue := 15, leftPreimage := 15, rightPreimage := 49, direction := 62,
          geoLeftImage := 15, geoRightImage := 49 }
      , { fiberValue := 16, leftPreimage := 16, rightPreimage := 50, direction := 34,
          geoLeftImage := 50, geoRightImage := 16 }
      , { fiberValue := 17, leftPreimage := 17, rightPreimage := 51, direction := 34,
          geoLeftImage := 51, geoRightImage := 17 }
      , { fiberValue := 18, leftPreimage := 18, rightPreimage := 52, direction := 38,
          geoLeftImage := 18, geoRightImage := 52 }
      , { fiberValue := 19, leftPreimage := 19, rightPreimage := 53, direction := 38,
          geoLeftImage := 19, geoRightImage := 53 }
      , { fiberValue := 20, leftPreimage := 20, rightPreimage := 54, direction := 34,
          geoLeftImage := 54, geoRightImage := 20 } ] ∧
      terminalFoldbin6TwoPointFiberDirectionSpectrum = ({34, 38, 62} : Finset Nat) ∧
      terminalFoldbin6FiberValuesByDirection 34 = [13, 16, 17, 20] ∧
      terminalFoldbin6FiberValuesByDirection 38 = [18, 19] ∧
      terminalFoldbin6FiberValuesByDirection 62 = [14, 15] ∧
      terminalFoldbin6GeoSwapFiberValues = terminalFoldbin6FiberValuesByDirection 34 := by
  native_decide

end Omega.GU
