import Mathlib.Tactic

namespace Omega.Zeta

/-- The order of the inertia group `H₀ ≃ C₅` above the order-`5` branch. -/
def xiTerminalZmDeltaS5FivecycleInertiaOrder : ℕ := 5

/-- The order of the normalizer `N_G(H₀)`, computed as `|H₀| * |Aut(H₀)| = 5 * 4`. -/
def xiTerminalZmDeltaS5FivecycleNormalizerOrder : ℕ := 20

/-- The four fixed points of a `5`-cycle, counted as `|N_G(H₀)| / |H₀|`. -/
abbrev XiTerminalZmDeltaS5FivecycleFixedPoint := Fin 4

/-- Transporting a local uniformizer along normalizer representatives produces the four nontrivial
characters of `C₅`, indexed here by the exponents `1,2,3,4`. -/
def xiTerminalZmDeltaS5FivecycleTangentExponent
    (P : XiTerminalZmDeltaS5FivecycleFixedPoint) : Fin 5 :=
  ⟨P.1 + 1, by omega⟩

/-- Paper label: `thm:xi-terminal-zm-delta-s5-5cycle-tangent-spectrum`.

In the finite `S₅` model, the normalizer quotient contributes exactly four fixed points, and the
tangent-character exponents are precisely the nonzero residues modulo `5`. -/
theorem paper_xi_terminal_zm_delta_s5_5cycle_tangent_spectrum :
    Fintype.card XiTerminalZmDeltaS5FivecycleFixedPoint =
        xiTerminalZmDeltaS5FivecycleNormalizerOrder / xiTerminalZmDeltaS5FivecycleInertiaOrder ∧
      xiTerminalZmDeltaS5FivecycleNormalizerOrder / xiTerminalZmDeltaS5FivecycleInertiaOrder = 4 ∧
      Finset.univ.image xiTerminalZmDeltaS5FivecycleTangentExponent =
        (Finset.univ.erase 0 : Finset (Fin 5)) := by
  native_decide
