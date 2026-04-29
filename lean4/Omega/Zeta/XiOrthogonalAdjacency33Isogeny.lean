import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.Zeta.XiFlagFactorization12x4x3

namespace Omega.Zeta

/-- The `13` lines inside the three-dimensional orthogonal complement `ℓ⊥`. -/
abbrev xi_orthogonal_adjacency_33_isogeny_lines_in_perp := Fin 13

/-- Removing the distinguished line `ℓ` leaves the `12` orthogonal neighbors `ℓ' ⊂ ℓ⊥`,
`ℓ' ≠ ℓ`. -/
abbrev xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors :=
  {L : xi_orthogonal_adjacency_33_isogeny_lines_in_perp // L ≠ 0}

/-- A basis for the two-dimensional isotropic plane `ℓ ⊕ ℓ'`. -/
abbrev xi_orthogonal_adjacency_33_isogeny_lagrangian_basis := Fin 2

/-- Each summand line contributes an order-`3` factor. -/
abbrev xi_orthogonal_adjacency_33_isogeny_line_factor := Fin 3

/-- The `(3,3)`-isogeny kernel attached to `ℓ ⊕ ℓ'`. -/
abbrev xi_orthogonal_adjacency_33_isogeny_kernel
    (_ : xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors) :=
  xi_orthogonal_adjacency_33_isogeny_line_factor ×
    xi_orthogonal_adjacency_33_isogeny_line_factor

/-- Concrete orthogonal-adjacency / `(3,3)`-isogeny package. -/
def xi_orthogonal_adjacency_33_isogeny_statement : Prop :=
  Fintype.card xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors = 12 ∧
    Nonempty
      (xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors ≃
        xi_flag_factorization_12_4x3_orthogonal_neighbors) ∧
    (∀ lPrime : xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors,
      Fintype.card (xi_orthogonal_adjacency_33_isogeny_kernel lPrime) = 9 ∧
        Fintype.card xi_orthogonal_adjacency_33_isogeny_lagrangian_basis = 2)

/-- Paper label: `prop:xi-orthogonal-adjacency-33-isogeny`. -/
theorem paper_xi_orthogonal_adjacency_33_isogeny :
    xi_orthogonal_adjacency_33_isogeny_statement := by
  refine ⟨by
      simp [xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors,
        xi_orthogonal_adjacency_33_isogeny_lines_in_perp],
    ?_, ?_⟩
  · refine ⟨(Fintype.equivFin
      xi_orthogonal_adjacency_33_isogeny_orthogonal_neighbors).trans ?_⟩
    exact (Fintype.equivFin xi_flag_factorization_12_4x3_orthogonal_neighbors).symm
  · intro lPrime
    simp [xi_orthogonal_adjacency_33_isogeny_kernel,
      xi_orthogonal_adjacency_33_isogeny_line_factor,
      xi_orthogonal_adjacency_33_isogeny_lagrangian_basis]

end Omega.Zeta
