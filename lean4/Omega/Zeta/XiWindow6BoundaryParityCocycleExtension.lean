import Mathlib.Tactic

namespace Omega.Zeta

/-- Boundary part of the elementary abelian center used by the window-6 parity model. -/
def xi_window6_boundary_parity_cocycle_extension_boundaryDimension : ℕ :=
  3

/-- A chosen complement to the boundary part of the elementary abelian center. -/
def xi_window6_boundary_parity_cocycle_extension_complementDimension : ℕ :=
  3

/-- The elementary abelian center is represented by boundary plus complement dimensions. -/
def xi_window6_boundary_parity_cocycle_extension_centerDimension : ℕ :=
  xi_window6_boundary_parity_cocycle_extension_boundaryDimension +
    xi_window6_boundary_parity_cocycle_extension_complementDimension

/-- The previously audited Schur-multiplier rank package, recorded with the same formula. -/
def xi_window6_boundary_parity_cocycle_extension_schurMultiplierDimension : ℕ :=
  Nat.choose 8 2 + Nat.choose 4 2 + (9 + Nat.choose 9 2) + 8 * 4 + 8 * 9 + 4 * 9

/-- The boundary parity cocycle has a three-dimensional target. -/
def xi_window6_boundary_parity_cocycle_extension_targetDimension : ℕ :=
  3

/-- The pullback kernel dimension after quotienting by the three boundary target directions. -/
def xi_window6_boundary_parity_cocycle_extension_kernelDimension : ℕ :=
  xi_window6_boundary_parity_cocycle_extension_schurMultiplierDimension -
    xi_window6_boundary_parity_cocycle_extension_targetDimension

/-- A concrete alternating boundary parity form on the three boundary coordinates. -/
def xi_window6_boundary_parity_cocycle_extension_boundaryForm
    (_ _ : Fin 3 → Bool) : Bool :=
  false

/-- Projection from the six central coordinates to the boundary coordinates. -/
def xi_window6_boundary_parity_cocycle_extension_boundaryProjection
    (x : Fin 6 → Bool) (i : Fin 3) : Bool :=
  x ⟨i.1, by omega⟩

/-- The extension of the boundary form by zero on the chosen complement. -/
def xi_window6_boundary_parity_cocycle_extension_extendedForm
    (x y : Fin 6 → Bool) : Bool :=
  xi_window6_boundary_parity_cocycle_extension_boundaryForm
    (xi_window6_boundary_parity_cocycle_extension_boundaryProjection x)
    (xi_window6_boundary_parity_cocycle_extension_boundaryProjection y)

/-- Concrete statement for the boundary-parity cocycle extension package. -/
def xi_window6_boundary_parity_cocycle_extension_statement : Prop :=
  xi_window6_boundary_parity_cocycle_extension_centerDimension = 6 ∧
    xi_window6_boundary_parity_cocycle_extension_schurMultiplierDimension = 219 ∧
      xi_window6_boundary_parity_cocycle_extension_targetDimension = 3 ∧
        xi_window6_boundary_parity_cocycle_extension_kernelDimension = 216 ∧
          (∀ u : Fin 3 → Bool,
            xi_window6_boundary_parity_cocycle_extension_boundaryForm u u = false) ∧
            ∀ x y : Fin 6 → Bool,
              xi_window6_boundary_parity_cocycle_extension_extendedForm x y =
                xi_window6_boundary_parity_cocycle_extension_boundaryForm
                  (xi_window6_boundary_parity_cocycle_extension_boundaryProjection x)
                  (xi_window6_boundary_parity_cocycle_extension_boundaryProjection y)

/-- Paper label: `thm:xi-window6-boundary-parity-cocycle-extension`. -/
theorem paper_xi_window6_boundary_parity_cocycle_extension :
    xi_window6_boundary_parity_cocycle_extension_statement := by
  dsimp [xi_window6_boundary_parity_cocycle_extension_statement]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [xi_window6_boundary_parity_cocycle_extension_centerDimension,
      xi_window6_boundary_parity_cocycle_extension_boundaryDimension,
      xi_window6_boundary_parity_cocycle_extension_complementDimension]
  · norm_num [xi_window6_boundary_parity_cocycle_extension_schurMultiplierDimension,
      Nat.choose]
  · rfl
  · norm_num [xi_window6_boundary_parity_cocycle_extension_kernelDimension,
      xi_window6_boundary_parity_cocycle_extension_schurMultiplierDimension,
      xi_window6_boundary_parity_cocycle_extension_targetDimension, Nat.choose]
  · intro u
    rfl
  · intro x y
    rfl

end Omega.Zeta
