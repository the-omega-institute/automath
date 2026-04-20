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

/-- The semisimple Lie-algebra target keeps exactly the non-scalar fixed blocks. -/
def window6GeoLocalSemisimpleBlockSizes (c : Window6GeoOrbitChargeClass) : List Nat :=
  (window6GeoLocalFixedBlockSizes c).filter fun n => 1 < n

/-- A nontrivial two-cycle block contributes the residual `u(1)` compression channel. -/
def window6GeoLocalCentralU1Rank (c : Window6GeoOrbitChargeClass) : Nat :=
  if c.twoCycles = 0 then 0 else 1

/-- Paper wrapper for the explicit Wedderburn counts of the `σ_geo`-fixed window-6 algebra.
    thm:terminal-window6-geo-fixed-subalgebra-wedderburn -/
theorem paper_terminal_window6_geo_fixed_subalgebra_wedderburn :
    window6GeoFixedScalarBlocks = 14 ∧ window6GeoFixedM2Blocks = 12 ∧
      window6GeoFixedM3Blocks = 6 ∧ window6GeoFixedM4Blocks = 2 ∧
      window6GeoFixedConnectedAutPU2Factors = 12 ∧
      window6GeoFixedConnectedAutPU3Factors = 6 ∧
      window6GeoFixedConnectedAutPU4Factors = 2 := by
  native_decide

set_option maxHeartbeats 400000 in
/-- Paper-facing wrapper for the local symmetry-compression patterns forced by the audited
window-`6` orbit-charge histogram: the fixed algebra block decomposition
`M_(f+p)(ℂ) ⊕ M_p(ℂ)` compresses the semisimple Lie part to the non-scalar blocks, with one
residual `u(1)` channel whenever a two-cycle block is present.
    cor:terminal-window6-geo-orbit-charge-symmetry-compression -/
theorem paper_terminal_window6_geo_orbit_charge_symmetry_compression :
    ⟨2, 1, 4⟩ ∈ window6GeoOrbitChargeHistogram ∧
      window6GeoLocalFixedBlockSizes ⟨2, 1, 4⟩ = [3, 1] ∧
      window6GeoLocalSemisimpleBlockSizes ⟨2, 1, 4⟩ = [3] ∧
      window6GeoLocalCentralU1Rank ⟨2, 1, 4⟩ = 1 ∧
      ⟨0, 2, 3⟩ ∈ window6GeoOrbitChargeHistogram ∧
      window6GeoLocalFixedBlockSizes ⟨0, 2, 3⟩ = [2, 2] ∧
      window6GeoLocalSemisimpleBlockSizes ⟨0, 2, 3⟩ = [2, 2] ∧
      window6GeoLocalCentralU1Rank ⟨0, 2, 3⟩ = 1 ∧
      ⟨1, 1, 2⟩ ∈ window6GeoOrbitChargeHistogram ∧
      window6GeoLocalFixedBlockSizes ⟨1, 1, 2⟩ = [2, 1] ∧
      window6GeoLocalSemisimpleBlockSizes ⟨1, 1, 2⟩ = [2] ∧
      window6GeoLocalCentralU1Rank ⟨1, 1, 2⟩ = 1 := by
  native_decide

/-- Paper wrapper for the exact orbit-charge census attached to the geometric window-`6`
stabilizer.
    cor:terminal-foldbin6-geo-orbit-charge -/
theorem paper_terminal_foldbin6_geo_orbit_charge :
    window6GeoOrbitChargeHistogram =
      [{ fixedPoints := 0, twoCycles := 1, multiplicity := 4 },
        { fixedPoints := 2, twoCycles := 0, multiplicity := 4 },
        { fixedPoints := 1, twoCycles := 1, multiplicity := 2 },
        { fixedPoints := 3, twoCycles := 0, multiplicity := 2 },
        { fixedPoints := 0, twoCycles := 2, multiplicity := 3 },
        { fixedPoints := 2, twoCycles := 1, multiplicity := 4 },
        { fixedPoints := 4, twoCycles := 0, multiplicity := 2 }] := by
  rfl

end Omega.GU
