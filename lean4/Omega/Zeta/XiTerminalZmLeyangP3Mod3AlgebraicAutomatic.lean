import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmLeyangPerronP3SemistableDegreeDrop

namespace Omega.Zeta

/-- The mod-`3` reduction of the renormalized `p = 3` Perron equation. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_special_fiber
    (u v : ZMod 3) : ZMod 3 :=
  xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_special_fiber u v

/-- Solving the reduced cubic for `u` gives the algebraic special-fiber branch map. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_cubic_cover
    (v : ZMod 3) : ZMod 3 :=
  xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_cubic_cover v

/-- The `v`-derivative of the reduced cubic equation. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_formal_derivative
    (v : ZMod 3) : ZMod 3 :=
  xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative v

/-- Finite lookup table for the special-fiber branch values. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_lookup_table :
    Fin 3 → ZMod 3
  | 0 => 0
  | 1 => 2
  | 2 => 0

/-- Explicit zero locus of the reduced cubic graph over `𝔽₃`. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus :
    Finset (ZMod 3 × ZMod 3) :=
  Finset.univ.filter fun p =>
    xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_special_fiber p.1 p.2 = 0

/-- Explicit graph of the cubic cover on `𝔽₃`; this is the finite automatic presentation. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus_expected :
    Finset (ZMod 3 × ZMod 3) :=
  {((0 : ZMod 3), (0 : ZMod 3)), ((2 : ZMod 3), (1 : ZMod 3)), ((0 : ZMod 3), (2 : ZMod 3))}

/-- Concrete paper-facing formulation of the mod-`3` algebraic/automatic package. -/
def xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_statement : Prop :=
  (∀ u v : ZMod 3,
      xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_special_fiber u v =
        u + v ^ 3 - v ^ 2 + v) ∧
    (∀ u v : ZMod 3,
      xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_special_fiber u v = 0 ↔
        u = xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_cubic_cover v) ∧
    xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_formal_derivative 0 = 2 ∧
    xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_formal_derivative 0 ≠ 0 ∧
    (∀ i : Fin 3,
      xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_cubic_cover (i : ZMod 3) =
        xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_lookup_table i) ∧
    xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus =
      xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_zero_locus_expected

/-- The scale-`27` Hensel package reduces mod `3` to the cubic equation
`v^3 - v^2 + v + u = 0`; the derivative at the origin is nonzero, and over the finite field
`𝔽₃` the resulting branch graph is an explicit finite lookup table.
    thm:xi-terminal-zm-leyang-perron-p3-mod3-algebraic-automatic -/
theorem paper_xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic :
    xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_statement := by
  rcases paper_xi_terminal_zm_leyang_perron_p3_semistable_degree_drop with
    ⟨_, _, hzero, hderiv, _⟩
  refine ⟨?_, hzero, ?_, ?_, ?_, ?_⟩
  · intro u v
    rfl
  · simpa [xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_formal_derivative] using
      hderiv 0
  · norm_num [xi_terminal_zm_leyang_perron_p3_mod3_algebraic_automatic_formal_derivative,
      xi_terminal_zm_leyang_perron_p3_semistable_degree_drop_formal_derivative]
  · intro i
    fin_cases i <;> native_decide
  · native_decide

end Omega.Zeta
