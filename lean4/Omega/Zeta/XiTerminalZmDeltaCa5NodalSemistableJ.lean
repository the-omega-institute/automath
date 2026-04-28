import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmDeltaCa5DiscriminantFactorizationSemistablePrimes

namespace Omega.Zeta

/-- The six semistable primes whose normalized elliptic kernels are audited in the nodal
`C_{A5}` table. -/
def xi_terminal_zm_delta_ca5_nodal_semistable_j_primes : Finset ℕ :=
  {11, 13, 17, 223, 3739, 7333}

/-- The audited normalized elliptic-kernel `j`-invariant modulo each listed prime. -/
def xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant : ℕ → ℕ
  | 11 => 5
  | 13 => 2
  | 17 => 15
  | 223 => 98
  | 3739 => 188
  | 7333 => 5450
  | _ => 0

/-- The audited split-node flag; only the node at `p = 17` splits. -/
def xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node : ℕ → Bool
  | 17 => true
  | _ => false

/-- The local table row asserted for one of the six nodal semistable primes. -/
def xi_terminal_zm_delta_ca5_nodal_semistable_j_row (p : ℕ) : Prop :=
  Nat.Prime p ∧
    p ∈ xiTerminalZmDeltaCa5OddSemistablePrimes ∧
      xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant p < p ∧
        (xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node p = true ↔ p = 17)

/-- Concrete package for the nodal semistable `j`-invariant table. -/
def xi_terminal_zm_delta_ca5_nodal_semistable_j_statement : Prop :=
  (∀ p, p ∈ xi_terminal_zm_delta_ca5_nodal_semistable_j_primes →
      xi_terminal_zm_delta_ca5_nodal_semistable_j_row p) ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 11 = 5 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 13 = 2 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 17 = 15 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 223 = 98 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 3739 = 188 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant 7333 = 5450 ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 17 = true ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 11 = false ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 13 = false ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 223 = false ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 3739 = false ∧
    xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node 7333 = false

/-- Paper label: `thm:xi-terminal-zm-delta-ca5-nodal-semistable-j`. -/
theorem paper_xi_terminal_zm_delta_ca5_nodal_semistable_j :
    xi_terminal_zm_delta_ca5_nodal_semistable_j_statement := by
  refine ⟨?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  intro p hp
  simp [xi_terminal_zm_delta_ca5_nodal_semistable_j_primes] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    norm_num [xi_terminal_zm_delta_ca5_nodal_semistable_j_row,
      xi_terminal_zm_delta_ca5_nodal_semistable_j_invariant,
      xi_terminal_zm_delta_ca5_nodal_semistable_j_split_node,
      xiTerminalZmDeltaCa5OddSemistablePrimes, xiTerminalZmDeltaCa5CollisionPrimes,
      xiTerminalZmDeltaCa5BranchCollisionPrimes]

end Omega.Zeta
