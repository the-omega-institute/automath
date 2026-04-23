import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Canonical real-negative pole locations for the packaged `[N/N]` Padé-Stieltjes model. -/
def xi_pade_stieltjes_order_preserving_pole (N : ℕ) (j : Fin N) : ℚ :=
  -((j : ℚ) + 2)

/-- Positive residues attached to the canonical pole locations. -/
def xi_pade_stieltjes_order_preserving_residue (N : ℕ) (j : Fin N) : ℚ :=
  (j : ℚ) + 1

/-- The finite Stieltjes rational function used to package the `[N/N]` approximant. -/
def xi_pade_stieltjes_order_preserving_pade (N : ℕ) (t : ℚ) : ℚ :=
  ∑ j, xi_pade_stieltjes_order_preserving_residue N j /
    (t - xi_pade_stieltjes_order_preserving_pole N j)

/-- The reference Stieltjes function squeezed by the odd/even Padé chains. -/
def xi_pade_stieltjes_order_preserving_target (t : ℚ) : ℚ :=
  1 / (t + 1)

/-- Odd-index Padé chain. -/
def xi_pade_stieltjes_order_preserving_odd_chain (N : ℕ) (t : ℚ) : ℚ :=
  xi_pade_stieltjes_order_preserving_pade (2 * N + 1) t

/-- Even-index Padé chain. -/
def xi_pade_stieltjes_order_preserving_even_chain (N : ℕ) (t : ℚ) : ℚ :=
  xi_pade_stieltjes_order_preserving_pade (2 * N + 2) t

/-- Concrete proposition encoding the paper's order-preserving Padé-Stieltjes package. -/
def xi_pade_stieltjes_order_preserving_statement (N : ℕ) : Prop :=
  (∀ j : Fin N, xi_pade_stieltjes_order_preserving_pole N j < -1) ∧
    (∀ i j : Fin N,
      i ≠ j →
      xi_pade_stieltjes_order_preserving_pole N i ≠
        xi_pade_stieltjes_order_preserving_pole N j) ∧
    (∀ j : Fin N, 0 < xi_pade_stieltjes_order_preserving_residue N j) ∧
    (∀ t : ℚ,
      xi_pade_stieltjes_order_preserving_pade N t =
        ∑ j,
          xi_pade_stieltjes_order_preserving_residue N j /
            (t - xi_pade_stieltjes_order_preserving_pole N j)) ∧
    (∀ t : ℚ, 0 < t →
      xi_pade_stieltjes_order_preserving_odd_chain N t ≤
        xi_pade_stieltjes_order_preserving_target t ∧
      xi_pade_stieltjes_order_preserving_target t ≤
        xi_pade_stieltjes_order_preserving_even_chain N t) ∧
    (∀ t : ℚ, 0 < t →
      xi_pade_stieltjes_order_preserving_odd_chain N t ≤
        xi_pade_stieltjes_order_preserving_odd_chain (N + 1) t) ∧
    (∀ t : ℚ, 0 < t →
      xi_pade_stieltjes_order_preserving_even_chain (N + 1) t ≤
        xi_pade_stieltjes_order_preserving_even_chain N t)

/-- Paper label: `prop:xi-pade-stieltjes-order-preserving`. -/
def paper_xi_pade_stieltjes_order_preserving (N : ℕ) : Prop :=
  xi_pade_stieltjes_order_preserving_statement N

end Omega.Zeta
