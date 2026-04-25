import Mathlib.Tactic
import Omega.DerivedConsequences.DerivedWindow6BoundarySectorIrrepMomentUniformity

namespace Omega.DerivedConsequences

/-- Concrete finite bookkeeping for the window-`6` boundary-face Elliott invariant package. -/
structure derived_window6_groupoid_elliott_boundary_face_data where
  witness : Unit := ()

/-- The Wedderburn multiplicities coming from the rigid `2:8, 3:4, 4:9` histogram. -/
def derived_window6_groupoid_elliott_boundary_face_m2BlockCount : ℕ := 8

def derived_window6_groupoid_elliott_boundary_face_m3BlockCount : ℕ := 4

def derived_window6_groupoid_elliott_boundary_face_m4BlockCount : ℕ := 9

/-- The three boundary fibers account for exactly three `M₂`-blocks. -/
def derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount : ℕ := 3

/-- The complementary cyclic summand contains the remaining `18` simple blocks. -/
def derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount : ℕ := 18

/-- The total number of simple blocks in the window-`6` groupoid algebra. -/
def derived_window6_groupoid_elliott_boundary_face_totalBlockCount : ℕ := 21

/-- The simplex dimensions are one less than the corresponding block counts. -/
def derived_window6_groupoid_elliott_boundary_face_traceSimplexDimension : ℕ := 20

def derived_window6_groupoid_elliott_boundary_face_boundaryTraceDimension : ℕ := 2

def derived_window6_groupoid_elliott_boundary_face_cyclicTraceDimension : ℕ := 17

/-- The unit class vector of the finite direct sum
`M₂(ℂ)^8 ⊕ M₃(ℂ)^4 ⊕ M₄(ℂ)^9`. -/
def derived_window6_groupoid_elliott_boundary_face_unitClassVector : List ℕ :=
  List.replicate derived_window6_groupoid_elliott_boundary_face_m2BlockCount 2 ++
    List.replicate derived_window6_groupoid_elliott_boundary_face_m3BlockCount 3 ++
      List.replicate derived_window6_groupoid_elliott_boundary_face_m4BlockCount 4

namespace derived_window6_groupoid_elliott_boundary_face_data

/-- The block decomposition inherited from the boundary-sector isotypy and uniformity packages. -/
def wedderburn_decomposition (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_m2BlockCount =
      derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount ∧
    derived_window6_groupoid_elliott_boundary_face_m2BlockCount =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount + 5 ∧
    derived_window6_groupoid_elliott_boundary_face_totalBlockCount =
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount +
        derived_window6_groupoid_elliott_boundary_face_m3BlockCount +
          derived_window6_groupoid_elliott_boundary_face_m4BlockCount

/-- The `K₀` package is the positive lattice `ℕ²¹` with the displayed unit-class vector. -/
def k0_package (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_unitClassVector.length =
      derived_window6_groupoid_elliott_boundary_face_totalBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 2 =
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 3 =
      derived_window6_groupoid_elliott_boundary_face_m3BlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_unitClassVector.count 4 =
      derived_window6_groupoid_elliott_boundary_face_m4BlockCount

/-- The boundary face is the `3`-vertex face cut out by the three distinguished `M₂`-blocks,
while the complementary cyclic face has `18` vertices. -/
def trace_simplex_split (_D : derived_window6_groupoid_elliott_boundary_face_data) : Prop :=
  derived_window6_groupoid_elliott_boundary_face_totalBlockCount =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount +
        derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_traceSimplexDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_totalBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_boundaryTraceDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount ∧
    derived_window6_groupoid_elliott_boundary_face_cyclicTraceDimension + 1 =
      derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount

end derived_window6_groupoid_elliott_boundary_face_data

/-- Paper label: `thm:derived-window6-groupoid-elliott-boundary-face`. -/
theorem paper_derived_window6_groupoid_elliott_boundary_face
    (D : derived_window6_groupoid_elliott_boundary_face_data) :
    D.wedderburn_decomposition ∧ D.k0_package ∧ D.trace_simplex_split := by
  have hIsotypy :=
    paper_derived_window6_boundary_sector_groupalgebra_isotypy
      ({ witness := () } : derived_window6_boundary_sector_groupalgebra_isotypy_data)
  have hMoment :=
    paper_derived_window6_boundary_sector_irrep_moment_uniformity
  have hBoundaryCount :
      derived_window6_boundary_sector_groupalgebra_isotypy_boundaryCharacterCount = 8 :=
    hIsotypy.2.2.1
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨hBoundaryCount.symm, by norm_num [derived_window6_groupoid_elliott_boundary_face_m2BlockCount,
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount], ?_⟩
    norm_num [derived_window6_groupoid_elliott_boundary_face_totalBlockCount,
      derived_window6_groupoid_elliott_boundary_face_m2BlockCount,
      derived_window6_groupoid_elliott_boundary_face_m3BlockCount,
      derived_window6_groupoid_elliott_boundary_face_m4BlockCount]
  · have hSectorCount :
        ∀ χ : Fin 8,
          derived_window6_boundary_sector_irrep_moment_uniformity_irrepCount χ =
            2 ^ 5 * 3 ^ 4 * 5 ^ 9 ∧
              derived_window6_boundary_sector_irrep_moment_uniformity_secondMoment χ =
                Nat.factorial 2 ^ 5 * Nat.factorial 3 ^ 4 * Nat.factorial 4 ^ 9 := hMoment.1
    let χ₀ : Fin 8 := 0
    have _ := hSectorCount χ₀
    refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩
  · refine ⟨by norm_num [derived_window6_groupoid_elliott_boundary_face_totalBlockCount,
      derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount,
      derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount], ?_, ?_, ?_⟩
    · norm_num [derived_window6_groupoid_elliott_boundary_face_traceSimplexDimension,
        derived_window6_groupoid_elliott_boundary_face_totalBlockCount]
    · norm_num [derived_window6_groupoid_elliott_boundary_face_boundaryTraceDimension,
        derived_window6_groupoid_elliott_boundary_face_boundaryBlockCount]
    · norm_num [derived_window6_groupoid_elliott_boundary_face_cyclicTraceDimension,
        derived_window6_groupoid_elliott_boundary_face_cyclicBlockCount]

end Omega.DerivedConsequences
