import Mathlib.Data.Matrix.Basic
import Omega.GU.Window6EdgeFluxFullMatrixSaturation

namespace Omega.GU

open Matrix

/-- The diagonal coordinate projector onto the span of the basis vectors indexed by `Y`. -/
def window6CoordinateProjector (Y : Finset (Fin 21)) : Matrix (Fin 21) (Fin 21) Real :=
  Matrix.diagonal fun i => if i ∈ Y then 1 else 0

/-- Paper: `cor:window6-exact-projector-synthesis`. -/
theorem paper_window6_exact_projector_synthesis
    (L : Fin 6 → Matrix (Fin 21) (Fin 21) Real) (hLie : Window6LieEnvelopeIsSl21 L)
    (Y : Finset (Fin 21)) : window6CoordinateProjector Y ∈ window6EdgeFluxClosure L := by
  exact paper_window6_edge_flux_full_matrix_saturation L hLie (window6CoordinateProjector Y)

end Omega.GU
