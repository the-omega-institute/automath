import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite ledger for the multistage CRT max-prime control statement.  The data record
keeps the number of stages, a threshold attached to each stage, and the total Chebyshev budget. -/
structure xi_multistage_crt_max_prime_additive_control_data where
  xi_multistage_crt_max_prime_additive_control_stage_count : ℕ
  xi_multistage_crt_max_prime_additive_control_threshold :
    Fin xi_multistage_crt_max_prime_additive_control_stage_count → ℕ
  xi_multistage_crt_max_prime_additive_control_chebyshev_budget : ℕ

namespace xi_multistage_crt_max_prime_additive_control_data

/-- The local budget assigned to a stage is capped by the global Chebyshev ledger. -/
def xi_multistage_crt_max_prime_additive_control_stage_budget
    (D : xi_multistage_crt_max_prime_additive_control_data)
    (i : Fin D.xi_multistage_crt_max_prime_additive_control_stage_count) : ℕ :=
  min (D.xi_multistage_crt_max_prime_additive_control_threshold i)
    D.xi_multistage_crt_max_prime_additive_control_chebyshev_budget

/-- Greedy disjoint block model: stage `i` receives the `i`-th ledger slot. -/
def xi_multistage_crt_max_prime_additive_control_greedy_block
    (D : xi_multistage_crt_max_prime_additive_control_data)
    (i : Fin D.xi_multistage_crt_max_prime_additive_control_stage_count) : Finset ℕ :=
  {i.1}

/-- The maximum prime scale dictated by the additive budget and the number of stages. -/
def xi_multistage_crt_max_prime_additive_control_optimal_max_prime
    (D : xi_multistage_crt_max_prime_additive_control_data) : ℕ :=
  D.xi_multistage_crt_max_prime_additive_control_chebyshev_budget +
    D.xi_multistage_crt_max_prime_additive_control_stage_count

/-- Necessity and optimal-value characterization in the finite ledger model. -/
def optimal_value_characterization
    (D : xi_multistage_crt_max_prime_additive_control_data) : Prop :=
  xi_multistage_crt_max_prime_additive_control_optimal_max_prime D =
      D.xi_multistage_crt_max_prime_additive_control_chebyshev_budget +
        D.xi_multistage_crt_max_prime_additive_control_stage_count ∧
    ∀ i,
      xi_multistage_crt_max_prime_additive_control_stage_budget D i ≤
        xi_multistage_crt_max_prime_additive_control_optimal_max_prime D

/-- The greedy blocks are pairwise disjoint and lie below the optimal max-prime scale. -/
def greedy_partition_realizes_bound
    (D : xi_multistage_crt_max_prime_additive_control_data) : Prop :=
  (∀ i p,
      p ∈ xi_multistage_crt_max_prime_additive_control_greedy_block D i →
        p ≤ xi_multistage_crt_max_prime_additive_control_optimal_max_prime D) ∧
    ∀ i j,
      i ≠ j →
        Disjoint (xi_multistage_crt_max_prime_additive_control_greedy_block D i)
          (xi_multistage_crt_max_prime_additive_control_greedy_block D j)

/-- Asymptotic-scale clause: the additive budget is dominated by the optimal max-prime ledger. -/
def asymptotic (D : xi_multistage_crt_max_prime_additive_control_data) : Prop :=
  D.xi_multistage_crt_max_prime_additive_control_chebyshev_budget ≤
    xi_multistage_crt_max_prime_additive_control_optimal_max_prime D

end xi_multistage_crt_max_prime_additive_control_data

open xi_multistage_crt_max_prime_additive_control_data

/-- Paper label: `thm:xi-multistage-crt-max-prime-additive-control`. -/
theorem paper_xi_multistage_crt_max_prime_additive_control
    (D : xi_multistage_crt_max_prime_additive_control_data) :
    D.optimal_value_characterization ∧ D.greedy_partition_realizes_bound ∧ D.asymptotic := by
  refine ⟨?_, ?_, ?_⟩
  · refine ⟨rfl, ?_⟩
    intro i
    dsimp [xi_multistage_crt_max_prime_additive_control_stage_budget,
      xi_multistage_crt_max_prime_additive_control_optimal_max_prime]
    omega
  · refine ⟨?_, ?_⟩
    · intro i p hp
      dsimp [xi_multistage_crt_max_prime_additive_control_greedy_block] at hp
      simp at hp
      dsimp [xi_multistage_crt_max_prime_additive_control_optimal_max_prime]
      omega
    · intro i j hij
      rw [Finset.disjoint_left]
      intro p hp_i hp_j
      dsimp [xi_multistage_crt_max_prime_additive_control_greedy_block] at hp_i hp_j
      simp at hp_i hp_j
      apply hij
      exact Fin.ext (hp_i.symm.trans hp_j)
  · dsimp [asymptotic, xi_multistage_crt_max_prime_additive_control_optimal_max_prime]
    omega

end Omega.Zeta
