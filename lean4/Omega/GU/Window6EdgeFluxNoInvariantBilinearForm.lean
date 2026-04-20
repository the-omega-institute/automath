import Mathlib.Tactic
import Omega.GU.Window6EdgeFluxFullMatrixSaturation

namespace Omega.GU

open Matrix

/-- If the edge-flux Lie envelope is all of `sl(21)`, then any bilinear form whose matrix
satisfies the infinitesimal invariance equation on the saturated closure is zero.
    prop:window6-edge-flux-no-invariant-bilinear-form -/
theorem paper_window6_edge_flux_no_invariant_bilinear_form
    (L : Fin 6 → Matrix (Fin 21) (Fin 21) Real) (hLie : Window6LieEnvelopeIsSl21 L) :
    ∀ S : Matrix (Fin 21) (Fin 21) Real,
      (∀ X : Matrix (Fin 21) (Fin 21) Real, X ∈ window6EdgeFluxClosure L →
        X.transpose * S + S * X = 0) →
      S = 0 := by
  intro S hInv
  have hfull := paper_window6_edge_flux_full_matrix_saturation L hLie
  have hI : (1 : Matrix (Fin 21) (Fin 21) Real) ∈ window6EdgeFluxClosure L := hfull 1
  have hEq :
      (1 : Matrix (Fin 21) (Fin 21) Real).transpose * S +
          S * (1 : Matrix (Fin 21) (Fin 21) Real) =
        0 := hInv 1 hI
  ext i j
  have hij : (2 : Real) * S i j = 0 := by
    have hEntry := congrArg (fun M : Matrix (Fin 21) (Fin 21) Real => M i j) hEq
    simpa [two_mul] using hEntry
  have hzero : S i j = 0 := by
    nlinarith [hij]
  simpa using hzero

end Omega.GU
