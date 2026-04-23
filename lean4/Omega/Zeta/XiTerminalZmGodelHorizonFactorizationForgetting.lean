import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Omega.Zeta.XiTerminalZmTateHypercubeSingleLayerVisibility

namespace Omega.Zeta

open scoped BigOperators

/-- Reuse the audited bit-vector model from the single-layer visibility theorem. -/
abbrev xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec (k : ℕ) :=
  xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k

/-- The two prime blocks are encoded by the same `Q_k × Q_k` carrier. -/
abbrev xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair (k : ℕ) :=
  xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion k

/-- The `n`-th prime, indexed from `0`. -/
noncomputable def xi_terminal_zm_godel_horizon_factorization_forgetting_nth_prime (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n

/-- Squarefree Gödel encoding of the first prime block. -/
noncomputable def xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_godel (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) : ℕ :=
  ∏ i : Fin k,
    xi_terminal_zm_godel_horizon_factorization_forgetting_nth_prime i.1 ^ (b i : ℕ)

/-- Squarefree Gödel encoding of the second prime block. -/
noncomputable def xi_terminal_zm_godel_horizon_factorization_forgetting_second_block_godel (k : ℕ)
    (c : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) : ℕ :=
  ∏ i : Fin k,
    xi_terminal_zm_godel_horizon_factorization_forgetting_nth_prime (k + i.1) ^ (c i : ℕ)

/-- Full squarefree Gödel encoding on `Q_k × Q_k`. -/
noncomputable def xi_terminal_zm_godel_horizon_factorization_forgetting_total_godel (k : ℕ)
    (x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k) : ℕ :=
  xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_godel k x.1 *
    xi_terminal_zm_godel_horizon_factorization_forgetting_second_block_godel k x.2

/-- Forget the second prime block. -/
def xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block (k : ℕ)
    (x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k) :
    xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k :=
  x.1

/-- The visible mod-`37` readout on the surviving layer. -/
def xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_readout (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) : ZMod 37 :=
  ∑ i : Fin k, (b i : ZMod 37)

/-- Fiber of the forgetful projection over a fixed first block. -/
def xi_terminal_zm_godel_horizon_factorization_forgetting_fiber (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) :=
  {x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k //
    xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block k x = b}

/-- The fibers of the forgetful projection are finite because they sit inside a finite product. -/
instance xi_terminal_zm_godel_horizon_factorization_forgetting_fiber_fintype (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) :
    Fintype (xi_terminal_zm_godel_horizon_factorization_forgetting_fiber k b) := by
  classical
  dsimp [xi_terminal_zm_godel_horizon_factorization_forgetting_fiber]
  infer_instance

/-- The total number of points collapsed to the bad-prime horizon value `6`. -/
def xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity
    (k : ℕ) : ℕ :=
  Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k) -
    Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k)

lemma xi_terminal_zm_godel_horizon_factorization_forgetting_total_godel_factorization (k : ℕ)
    (x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k) :
    xi_terminal_zm_godel_horizon_factorization_forgetting_total_godel k x =
      xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_godel k
          (xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block k x) *
        xi_terminal_zm_godel_horizon_factorization_forgetting_second_block_godel k x.2 := by
  rfl

lemma xi_terminal_zm_godel_horizon_factorization_forgetting_visible_factorization (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) :
    xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction k (b, 0) =
      xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_readout k
        (xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block k
          (b, 0)) := by
  simp [xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_readout,
    xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block,
    xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction]

def xi_terminal_zm_godel_horizon_factorization_forgetting_fiber_equiv_second_block (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) :
    xi_terminal_zm_godel_horizon_factorization_forgetting_fiber k b ≃
      xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k where
  toFun x := x.1.2
  invFun c := ⟨(b, c), rfl⟩
  left_inv x := by
    rcases x with ⟨⟨b', c⟩, hb'⟩
    cases hb'
    rfl
  right_inv c := rfl

lemma xi_terminal_zm_godel_horizon_factorization_forgetting_fiber_card (k : ℕ)
    (b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) :
    Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_fiber k b) = 2 ^ k := by
  calc
    Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_fiber k b) =
        Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k) := by
          exact Fintype.card_congr
            (xi_terminal_zm_godel_horizon_factorization_forgetting_fiber_equiv_second_block k b)
    _ = 2 ^ k := by
          change
            Fintype.card (xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec k) = 2 ^ k
          exact xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec_card k

lemma xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity_eq
    (k : ℕ) :
    xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity k =
      2 ^ (2 * k) - 2 ^ k := by
  unfold xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity
  rw [xi_terminal_zm_tate_hypercube_single_layer_visibility_torsion_card,
    xi_terminal_zm_tate_hypercube_single_layer_visibility_bitvec_card]

/-- Concrete proposition packaging the Gödel factorization, the visibility readout on the first
prime block, the uniform fiber size, and the bad-horizon collapse multiplicity. -/
def xi_terminal_zm_godel_horizon_factorization_forgetting_statement (k : Nat) : Prop :=
  (∀ x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k,
      xi_terminal_zm_godel_horizon_factorization_forgetting_total_godel k x =
        xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_godel k
            (xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block k x) *
          xi_terminal_zm_godel_horizon_factorization_forgetting_second_block_godel k x.2) ∧
    (∃ B : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k → ZMod 37,
      ∀ b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k,
        xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction k (b, 0) =
          B (xi_terminal_zm_godel_horizon_factorization_forgetting_forget_second_prime_block k
            (b, 0))) ∧
    (∀ x : xi_terminal_zm_godel_horizon_factorization_forgetting_encoded_pair k,
      x.2 ≠ 0 →
        xi_terminal_zm_tate_hypercube_single_layer_visibility_reduction k x = 6) ∧
    (∀ b : xi_terminal_zm_godel_horizon_factorization_forgetting_bitvec k,
      Fintype.card (xi_terminal_zm_godel_horizon_factorization_forgetting_fiber k b) = 2 ^ k) ∧
    xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity k =
      2 ^ (2 * k) - 2 ^ k

/-- Paper label: `prop:xi-terminal-zm-godel-horizon-factorization-forgetting`. -/
theorem paper_xi_terminal_zm_godel_horizon_factorization_forgetting (k : Nat) :
    xi_terminal_zm_godel_horizon_factorization_forgetting_statement k := by
  refine ⟨xi_terminal_zm_godel_horizon_factorization_forgetting_total_godel_factorization k,
    ?_, xi_terminal_zm_tate_hypercube_single_layer_visibility_collapse k,
    xi_terminal_zm_godel_horizon_factorization_forgetting_fiber_card k, ?_⟩
  · refine ⟨xi_terminal_zm_godel_horizon_factorization_forgetting_first_block_readout k, ?_⟩
    exact xi_terminal_zm_godel_horizon_factorization_forgetting_visible_factorization k
  · exact
      xi_terminal_zm_godel_horizon_factorization_forgetting_bad_horizon_collapse_multiplicity_eq k

end Omega.Zeta
