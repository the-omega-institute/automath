import Mathlib.Tactic
import Omega.Core.WalshStokesSingleton

namespace Omega.Zeta

abbrev xi_terminal_zm_lattes_preimage_hypercube_2k_bitvec (k : Nat) := Omega.Word k

abbrev xi_terminal_zm_lattes_preimage_hypercube_2k_torsor (k : Nat) :=
  xi_terminal_zm_lattes_preimage_hypercube_2k_bitvec k ×
    xi_terminal_zm_lattes_preimage_hypercube_2k_bitvec k

abbrev xi_terminal_zm_lattes_preimage_hypercube_2k_cube (k : Nat) := Omega.Word (2 * k)

private theorem xi_terminal_zm_lattes_preimage_hypercube_2k_torsor_card (k : Nat) :
    Fintype.card (xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k) = 2 ^ (2 * k) := by
  calc
    Fintype.card (xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k) = 2 ^ k * 2 ^ k := by
      simp [xi_terminal_zm_lattes_preimage_hypercube_2k_torsor,
        xi_terminal_zm_lattes_preimage_hypercube_2k_bitvec]
    _ = 2 ^ (k + k) := by rw [← pow_add]
    _ = 2 ^ (2 * k) := by congr 1; omega

noncomputable def xi_terminal_zm_lattes_preimage_hypercube_2k_address (k : Nat) :
    xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k ≃
      xi_terminal_zm_lattes_preimage_hypercube_2k_cube k :=
  Fintype.equivOfCardEq <| by
    rw [xi_terminal_zm_lattes_preimage_hypercube_2k_torsor_card]
    simp [xi_terminal_zm_lattes_preimage_hypercube_2k_cube]

noncomputable def xi_terminal_zm_lattes_preimage_hypercube_2k_flip_neighbor (k : Nat)
    (i : Fin (2 * k))
    (x : xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k) :
    xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k :=
  (xi_terminal_zm_lattes_preimage_hypercube_2k_address k).symm
    (Omega.Core.flipBit i ((xi_terminal_zm_lattes_preimage_hypercube_2k_address k) x))

def xi_terminal_zm_lattes_preimage_hypercube_2k_adjacent (k : Nat)
    (x y : xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k) : Prop :=
  ∃ i : Fin (2 * k),
    (xi_terminal_zm_lattes_preimage_hypercube_2k_address k) y =
      Omega.Core.flipBit i ((xi_terminal_zm_lattes_preimage_hypercube_2k_address k) x)

def xi_terminal_zm_lattes_preimage_hypercube_2k_statement (k : Nat) : Prop :=
  Nonempty
      (xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k ≃
        xi_terminal_zm_lattes_preimage_hypercube_2k_cube k) ∧
    Fintype.card (xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k) = 2 ^ (2 * k) ∧
    (∀ x : xi_terminal_zm_lattes_preimage_hypercube_2k_torsor k, ∀ i : Fin (2 * k),
      xi_terminal_zm_lattes_preimage_hypercube_2k_adjacent k x
        (xi_terminal_zm_lattes_preimage_hypercube_2k_flip_neighbor k i x)) ∧
    Fintype.card (xi_terminal_zm_lattes_preimage_hypercube_2k_torsor 3) = 64

/-- Paper label: `thm:xi-terminal-zm-lattes-preimage-hypercube-2k`. Modeling the `2^k`-torsion
torsor as two binary words gives `2^(2k)` preimages, and the induced preimage graph is the `2k`
cube after transporting coordinate flips along the address equivalence. -/
theorem paper_xi_terminal_zm_lattes_preimage_hypercube_2k (k : Nat) :
    xi_terminal_zm_lattes_preimage_hypercube_2k_statement k := by
  refine ⟨⟨xi_terminal_zm_lattes_preimage_hypercube_2k_address k⟩,
    xi_terminal_zm_lattes_preimage_hypercube_2k_torsor_card k, ?_, ?_⟩
  · intro x i
    refine ⟨i, ?_⟩
    simpa [xi_terminal_zm_lattes_preimage_hypercube_2k_flip_neighbor] using
      (xi_terminal_zm_lattes_preimage_hypercube_2k_address k).apply_symm_apply
        (Omega.Core.flipBit i ((xi_terminal_zm_lattes_preimage_hypercube_2k_address k) x))
  · simpa using xi_terminal_zm_lattes_preimage_hypercube_2k_torsor_card 3

end Omega.Zeta
