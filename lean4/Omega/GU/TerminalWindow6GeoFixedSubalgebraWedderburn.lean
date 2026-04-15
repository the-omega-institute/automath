import Mathlib.Tactic

namespace Omega.GU

/-- A single orbit-charge class for the window-6 geometric involution: `fixedPoints` counts
`1`-cycles, `twoCycles` counts `2`-cycles, and `multiplicity` records how many fibers realize
that charge. -/
structure Window6GeoOrbitChargeClass where
  fixedPoints : Nat
  twoCycles : Nat
  multiplicity : Nat
deriving DecidableEq, Repr

/-- The seven orbit-charge classes from the audited window-6 histogram
`(f_x, p_x, count) = (0,1,4), (2,0,4), (1,1,2), (3,0,2), (0,2,3), (2,1,4), (4,0,2)`. -/
def window6GeoOrbitChargeHistogram : List Window6GeoOrbitChargeClass :=
  [⟨0, 1, 4⟩, ⟨2, 0, 4⟩, ⟨1, 1, 2⟩, ⟨3, 0, 2⟩, ⟨0, 2, 3⟩, ⟨2, 1, 4⟩, ⟨4, 0, 2⟩]

/-- For a fiber with orbit charge `(f, p)`, the fixed subalgebra block sizes are
`M_(f+p)(ℂ) ⊕ M_p(ℂ)`. -/
def window6GeoLocalFixedBlockSizes (c : Window6GeoOrbitChargeClass) : List Nat :=
  [c.fixedPoints + c.twoCycles, c.twoCycles]

/-- Count the total multiplicity of blocks of matrix size `k` in the global fixed algebra. -/
def window6GeoFixedBlockCount (k : Nat) : Nat :=
  window6GeoOrbitChargeHistogram.foldl
    (fun acc c => acc + c.multiplicity * (window6GeoLocalFixedBlockSizes c).count k) 0

/-- Scalar blocks in the window-6 geometric fixed algebra. -/
def window6GeoFixedScalarBlocks : Nat :=
  window6GeoFixedBlockCount 1

/-- `M₂(ℂ)` blocks in the window-6 geometric fixed algebra. -/
def window6GeoFixedM2Blocks : Nat :=
  window6GeoFixedBlockCount 2

/-- `M₃(ℂ)` blocks in the window-6 geometric fixed algebra. -/
def window6GeoFixedM3Blocks : Nat :=
  window6GeoFixedBlockCount 3

/-- `M₄(ℂ)` blocks in the window-6 geometric fixed algebra. -/
def window6GeoFixedM4Blocks : Nat :=
  window6GeoFixedBlockCount 4

/-- The connected `Aut`-factor multiplicity contributed by the `M₂(ℂ)` blocks. -/
def window6GeoFixedConnectedAutPU2Factors : Nat :=
  window6GeoFixedM2Blocks

/-- The connected `Aut`-factor multiplicity contributed by the `M₃(ℂ)` blocks. -/
def window6GeoFixedConnectedAutPU3Factors : Nat :=
  window6GeoFixedM3Blocks

/-- The connected `Aut`-factor multiplicity contributed by the `M₄(ℂ)` blocks. -/
def window6GeoFixedConnectedAutPU4Factors : Nat :=
  window6GeoFixedM4Blocks

/-- Paper wrapper for the explicit Wedderburn counts of the `σ_geo`-fixed window-6 algebra.
    thm:terminal-window6-geo-fixed-subalgebra-wedderburn -/
theorem paper_terminal_window6_geo_fixed_subalgebra_wedderburn :
    window6GeoFixedScalarBlocks = 14 ∧ window6GeoFixedM2Blocks = 12 ∧
      window6GeoFixedM3Blocks = 6 ∧ window6GeoFixedM4Blocks = 2 ∧
      window6GeoFixedConnectedAutPU2Factors = 12 ∧
      window6GeoFixedConnectedAutPU3Factors = 6 ∧
      window6GeoFixedConnectedAutPU4Factors = 2 := by
  native_decide

end Omega.GU
