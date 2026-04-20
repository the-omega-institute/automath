import Mathlib.Data.Matrix.Action
import Mathlib.Tactic
import Omega.GU.Window6EdgeFluxFullMatrixSaturation

namespace Omega.GU

open Matrix

/-- The `21`-dimensional carrier used for the edge-flux dynamics wrappers. -/
abbrev Window6EdgeFluxCarrier := Fin 21 → Real

/-- Matrix action on the audited carrier. -/
def window6EdgeFluxAction (A : Matrix (Fin 21) (Fin 21) Real) (v : Window6EdgeFluxCarrier) :
    Window6EdgeFluxCarrier :=
  A *ᵥ v

/-- Concrete dynamics data for the window-`6` edge-flux action and an equivariant bilinear
product on the `21`-dimensional carrier. -/
structure Window6EdgeFluxDynamicsData where
  generators : Fin 6 → Matrix (Fin 21) (Fin 21) Real
  product : Window6EdgeFluxCarrier → Window6EdgeFluxCarrier → Window6EdgeFluxCarrier
  lieEnvelopeIsSl21 : Window6LieEnvelopeIsSl21 generators
  add_left :
    ∀ x₁ x₂ y, product (x₁ + x₂) y = product x₁ y + product x₂ y
  smul_left :
    ∀ (a : Real) x y, product (a • x) y = a • product x y
  add_right :
    ∀ x y₁ y₂, product x (y₁ + y₂) = product x y₁ + product x y₂
  smul_right :
    ∀ (a : Real) x y, product x (a • y) = a • product x y
  closureEquivariant :
    ∀ A, A ∈ window6EdgeFluxClosure generators →
      ∀ x y, product (window6EdgeFluxAction A x) (window6EdgeFluxAction A y) =
        window6EdgeFluxAction A (product x y)

/-- Any bilinear product invariant under the saturated edge-flux dynamics must vanish. -/
def Window6EdgeFluxDynamicsData.noInvariantBinaryProduct
    (D : Window6EdgeFluxDynamicsData) : Prop :=
  ∀ x y, D.product x y = 0

private lemma window6EdgeFluxAction_double
    (x : Window6EdgeFluxCarrier) :
    window6EdgeFluxAction ((2 : Real) • (1 : Matrix (Fin 21) (Fin 21) Real)) x = (2 : Real) • x := by
  unfold window6EdgeFluxAction
  rw [smul_mulVec, one_mulVec]

/-- Full matrix saturation identifies the generated dynamics with the full endomorphism algebra;
applying equivariance to the scalar matrix `2 • I` and comparing with bilinearity forces every
equivariant binary product to vanish.
    thm:window6-edge-flux-no-invariant-binary-product -/
theorem paper_window6_edge_flux_no_invariant_binary_product
    (D : Window6EdgeFluxDynamicsData) : D.noInvariantBinaryProduct := by
  have hfull := paper_window6_edge_flux_full_matrix_saturation D.generators D.lieEnvelopeIsSl21
  intro x y
  let A : Matrix (Fin 21) (Fin 21) Real := (2 : Real) • (1 : Matrix (Fin 21) (Fin 21) Real)
  have hA : A ∈ window6EdgeFluxClosure D.generators := hfull A
  have hEq :=
    D.closureEquivariant A hA x y
  have hscale :
      ((2 : Real) * 2) • D.product x y = (2 : Real) • D.product x y := by
    simpa [A, window6EdgeFluxAction_double, D.smul_left, D.smul_right, smul_smul] using hEq
  apply funext
  intro i
  have hi := congrFun hscale i
  have : D.product x y i = 0 := by
    have hi' : ((2 : Real) * 2) * D.product x y i = (2 : Real) * D.product x y i := by
      simpa [Pi.smul_apply] using hi
    linarith
  simpa using this

end Omega.GU
