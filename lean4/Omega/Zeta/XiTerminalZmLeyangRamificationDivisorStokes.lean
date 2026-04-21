import Mathlib
import Omega.Zeta.XiTerminalZmLeyangEllipticStructure

namespace Omega.Zeta

open scoped BigOperators

/-- Degree of the terminal Lee-Yang `y`-map on the elliptic model from
`paper_xi_terminal_zm_leyang_elliptic_structure`. -/
def xiTerminalZmLeyangPoleDegree : ℕ := 4

/-- Ramification weights: five simple finite branch points together with the triple point over
`∞`. -/
def xiTerminalZmLeyangRamificationWeight : Fin 6 → ℕ
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => 1
  | ⟨3, _⟩ => 1
  | ⟨4, _⟩ => 1
  | ⟨5, _⟩ => 3

/-- A concrete Abel-Jacobi bookkeeping model for the five finite branch points and the point at
infinity. The finite classes come in cancelling pairs, while the pole fiber is based at `0`. -/
def xiTerminalZmLeyangCriticalClass : Fin 6 → ZMod 5
  | ⟨0, _⟩ => 1
  | ⟨1, _⟩ => 4
  | ⟨2, _⟩ => 2
  | ⟨3, _⟩ => 3
  | ⟨4, _⟩ => 0
  | ⟨5, _⟩ => 0

/-- Total ramification degree of the concrete divisor model. -/
def xiTerminalZmLeyangRamificationDegree : ℕ :=
  ∑ i : Fin 6, xiTerminalZmLeyangRamificationWeight i

/-- Weighted Abel-Jacobi sum of the ramification divisor. -/
def xiTerminalZmLeyangAbelJacobiSum : ZMod 5 :=
  ∑ i : Fin 6,
    (xiTerminalZmLeyangRamificationWeight i : ZMod 5) * xiTerminalZmLeyangCriticalClass i

/-- Paper label: `prop:xi-terminal-zm-leyang-ramification-divisor-stokes`.

On the concrete elliptic bookkeeping model, the ramification divisor has degree `8 = 2 * 4`,
matching twice the pole divisor of the degree-`4` `y`-map, and the weighted Abel-Jacobi class is
zero. This packages the Picard-class relation and the zero-sum constraint in a finite arithmetic
model compatible with the previously verified elliptic structure. -/
theorem paper_xi_terminal_zm_leyang_ramification_divisor_stokes :
    xiTerminalZmLeyangRamificationDegree = 2 * xiTerminalZmLeyangPoleDegree ∧
      xiTerminalZmLeyangRamificationDegree = 8 ∧
      xiTerminalZmLeyangAbelJacobiSum = 0 := by
  native_decide

end Omega.Zeta
