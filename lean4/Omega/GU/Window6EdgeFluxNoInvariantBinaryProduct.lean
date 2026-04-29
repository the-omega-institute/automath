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

/-- Any nonzero bilinear bracket on the `21`-dimensional carrier that is equivariant for the full
window-`6` edge-flux dynamics is ruled out by the no-invariant-binary-product theorem. This is the
formal contradiction underlying the paper's Spin(7)/`so(7)` dynamic anomaly corollary.
    cor:window6-spin7-bracket-dynamic-anomaly -/
theorem paper_window6_spin7_bracket_dynamic_anomaly
    (generators : Fin 6 → Matrix (Fin 21) (Fin 21) Real)
    (bracket : Window6EdgeFluxCarrier → Window6EdgeFluxCarrier → Window6EdgeFluxCarrier)
    (hLie : Window6LieEnvelopeIsSl21 generators)
    (hAddLeft : ∀ x₁ x₂ y, bracket (x₁ + x₂) y = bracket x₁ y + bracket x₂ y)
    (hSmulLeft : ∀ (a : Real) x y, bracket (a • x) y = a • bracket x y)
    (hAddRight : ∀ x y₁ y₂, bracket x (y₁ + y₂) = bracket x y₁ + bracket x y₂)
    (hSmulRight : ∀ (a : Real) x y, bracket x (a • y) = a • bracket x y)
    (hEquivariant :
      ∀ A, A ∈ window6EdgeFluxClosure generators →
        ∀ x y, bracket (window6EdgeFluxAction A x) (window6EdgeFluxAction A y) =
          window6EdgeFluxAction A (bracket x y))
    (hNonabelian : ∃ x y, bracket x y ≠ 0) :
    False := by
  let D : Window6EdgeFluxDynamicsData := {
    generators := generators
    product := bracket
    lieEnvelopeIsSl21 := hLie
    add_left := hAddLeft
    smul_left := hSmulLeft
    add_right := hAddRight
    smul_right := hSmulRight
    closureEquivariant := hEquivariant
  }
  have hzero : D.noInvariantBinaryProduct := paper_window6_edge_flux_no_invariant_binary_product D
  rcases hNonabelian with ⟨x, y, hxy⟩
  exact hxy (hzero x y)

end Omega.GU
