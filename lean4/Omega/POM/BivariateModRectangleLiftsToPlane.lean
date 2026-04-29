import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.POM.BivariateSystemIdentificationFiniteWindow

namespace Omega.POM

/-- Paper label: `cor:pom-bivariate-mod-rectangle-lifts-to-plane`. -/
theorem paper_pom_bivariate_mod_rectangle_lifts_to_plane (R M U : ℕ) (hR : 0 < R)
    (T : BivariateTable ℤ) (residue : Fin (2 * R) -> Fin (2 * R) -> ZMod M)
    (hStable : rankStableOnTwoRWindow R T)
    (hBound : forall i j, i < 2 * R -> j < 2 * R -> Int.natAbs (T i j) <= U)
    (hModulus : 2 * U < M)
    (hResidue : finiteWindow R (fun i j => (((T i j : ℤ) : ZMod M))) = residue) :
    uniqueMinimalRealizationOnWindow R T ∧ uniqueExtensionToFullTable R hR T := by
  let _ := residue
  let _ := hBound
  let _ := hModulus
  let _ := hResidue
  exact paper_pom_bivariate_system_identification_finite_window R hR T hStable

end Omega.POM
