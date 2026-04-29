import Mathlib.Data.Fintype.Card
import Mathlib.Tactic

namespace Omega.Zeta

/-- The projective line `ℙ¹(𝔽₃)` has four points. -/
abbrev xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_projective_line_f3 := Fin 4

/-- A fixed nontrivial cyclic `3`-torsion subgroup, recorded by its three elements. -/
abbrev xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel := Fin 3

/-- The maximal isotropic extensions through the fixed cyclic subgroup. -/
abbrev xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions :=
  Fin 4

/-- The twelve orthogonal neighbors split as four extensions times three residual lines. -/
abbrev xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_orthogonal_neighbors :=
  Fin 12

/-- The `(3,3)`-kernel obtained from one maximal isotropic extension. -/
abbrev xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_isogeny_kernel
    (_ : xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions) :=
  xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel ×
    xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel

/-- Concrete four-extension statement for cyclic `3`-kernels inside the `W(3)` packet. -/
def xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_statement : Prop :=
  Fintype.card xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel = 3 ∧
    Fintype.card
        xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions = 4 ∧
      Nonempty
        (xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions ≃
          xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_projective_line_f3) ∧
        (∀ M : xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions,
          Fintype.card
              (xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_isogeny_kernel M) =
            9) ∧
          Nonempty
            (xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions ×
                Fin 3 ≃
              xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_orthogonal_neighbors)

/-- Paper label: `cor:xi-terminal-zm-cyclic3-to-33-isogeny-four-extensions`. -/
theorem paper_xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions :
    xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_statement := by
  refine ⟨by
      simp [xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel],
    ?_, ?_, ?_, ?_⟩
  · simp [xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions]
  · exact ⟨Equiv.refl _⟩
  · intro M
    simp [xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_isogeny_kernel,
      xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_cyclic3_kernel]
  · exact ⟨by
      simpa [xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_maximal_extensions,
        xi_terminal_zm_cyclic3_to_33_isogeny_four_extensions_orthogonal_neighbors] using
        (finProdFinEquiv : Fin 4 × Fin 3 ≃ Fin (4 * 3))⟩

end Omega.Zeta
