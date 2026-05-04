import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.GU.Window6CyclicWeightThresholdRootLength
import Omega.Zeta.XiWindow6B3C3TightFrameFourthMomentNonsimilarity

namespace Omega.Zeta

/-- Canonical finite data package for the window-`6` orbitwise `B₃/C₃` Langlands duality
dictionary.  The fields are fixed by the imported root dictionaries: axial `B₃` roots are sent to
axial `C₃` roots by doubling, and off-axis roots are fixed. -/
inductive xi_window6_b3c3_orbitwise_langlands_duality_data where
  | xi_window6_b3c3_orbitwise_langlands_duality_data_canonical

namespace xi_window6_b3c3_orbitwise_langlands_duality_data

/-- The signed-coordinate generator set used for the finite Weyl-equivariance check. -/
inductive xi_window6_b3c3_orbitwise_langlands_duality_signed_generator where
  | xi_window6_b3c3_orbitwise_langlands_duality_negX
  | xi_window6_b3c3_orbitwise_langlands_duality_negY
  | xi_window6_b3c3_orbitwise_langlands_duality_negZ
  | xi_window6_b3c3_orbitwise_langlands_duality_swapXY
  | xi_window6_b3c3_orbitwise_langlands_duality_swapXZ
  | xi_window6_b3c3_orbitwise_langlands_duality_swapYZ
deriving DecidableEq, Repr

/-- The six signed-coordinate generators as a finite checklist. -/
def xi_window6_b3c3_orbitwise_langlands_duality_signed_generators :
    List xi_window6_b3c3_orbitwise_langlands_duality_signed_generator :=
  [.xi_window6_b3c3_orbitwise_langlands_duality_negX,
    .xi_window6_b3c3_orbitwise_langlands_duality_negY,
    .xi_window6_b3c3_orbitwise_langlands_duality_negZ,
    .xi_window6_b3c3_orbitwise_langlands_duality_swapXY,
    .xi_window6_b3c3_orbitwise_langlands_duality_swapXZ,
    .xi_window6_b3c3_orbitwise_langlands_duality_swapYZ]

/-- Action of a signed-coordinate generator on a root. -/
def xi_window6_b3c3_orbitwise_langlands_duality_generator_action
    (g : xi_window6_b3c3_orbitwise_langlands_duality_signed_generator)
    (r : XiWindow6Root) : XiWindow6Root :=
  match g, r with
  | .xi_window6_b3c3_orbitwise_langlands_duality_negX, (x, y, z) => (-x, y, z)
  | .xi_window6_b3c3_orbitwise_langlands_duality_negY, (x, y, z) => (x, -y, z)
  | .xi_window6_b3c3_orbitwise_langlands_duality_negZ, (x, y, z) => (x, y, -z)
  | .xi_window6_b3c3_orbitwise_langlands_duality_swapXY, (x, y, z) => (y, x, z)
  | .xi_window6_b3c3_orbitwise_langlands_duality_swapXZ, (x, y, z) => (z, y, x)
  | .xi_window6_b3c3_orbitwise_langlands_duality_swapYZ, (x, y, z) => (x, z, y)

/-- The Langlands-duality map: double the axial `B₃` orbit and fix the off-axis orbit. -/
def duality_map (_D : xi_window6_b3c3_orbitwise_langlands_duality_data)
    (r : XiWindow6Root) : XiWindow6Root :=
  if r ∈ xiWindow6B3ShortRoots then
    (2 * r.1, 2 * r.2.1, 2 * r.2.2)
  else
    r

/-- The finite axial-orbit formulas for the `B₃` and `C₃` dictionaries. -/
def axis_orbit_formulas (D : xi_window6_b3c3_orbitwise_langlands_duality_data) : Prop :=
  xiWindow6B3ShortRoots.length = 6 ∧
    xiWindow6LongRoots.length = 6 ∧
    (xiWindow6B3ShortRoots.map D.duality_map).toFinset = xiWindow6LongRoots.toFinset

/-- The finite off-axis orbit formulas for the common twelve-root orbit. -/
def off_axis_orbit_formulas (D : xi_window6_b3c3_orbitwise_langlands_duality_data) : Prop :=
  xiWindow6ShortRoots.length = 12 ∧
    (xiWindow6ShortRoots.map D.duality_map).toFinset = xiWindow6ShortRoots.toFinset

/-- The duality map commutes with the signed-coordinate generators on the finite `B₃` root list. -/
def duality_map_equivariant (D : xi_window6_b3c3_orbitwise_langlands_duality_data) : Prop :=
  ((xi_window6_b3c3_orbitwise_langlands_duality_signed_generators.product xiWindow6B3Roots).all
    fun gr =>
      D.duality_map
          (xi_window6_b3c3_orbitwise_langlands_duality_generator_action gr.1 gr.2) ==
        xi_window6_b3c3_orbitwise_langlands_duality_generator_action gr.1 (D.duality_map gr.2)) =
    true

end xi_window6_b3c3_orbitwise_langlands_duality_data

open xi_window6_b3c3_orbitwise_langlands_duality_data

/-- Paper label: `thm:xi-window6-b3c3-orbitwise-langlands-duality`. -/
theorem paper_xi_window6_b3c3_orbitwise_langlands_duality
    (D : xi_window6_b3c3_orbitwise_langlands_duality_data) :
    D.axis_orbit_formulas ∧ D.off_axis_orbit_formulas ∧ D.duality_map_equivariant := by
  cases D
  unfold axis_orbit_formulas off_axis_orbit_formulas duality_map_equivariant
  repeat' constructor <;> native_decide

end Omega.Zeta
