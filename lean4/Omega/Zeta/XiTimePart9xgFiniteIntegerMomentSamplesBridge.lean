import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-sample data for the analytic-bridge non-determination statement. -/
structure xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data where
  sample_nodes : Finset ℕ
  base_bridge : ℕ → ℤ
  escape_node : ℕ
  escape_node_not_sample : escape_node ∉ sample_nodes

namespace xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data

/-- A concrete finite-sample vanishing perturbation.  It is zero on the sampled nodes and
nonzero at the packaged escape node. -/
def xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish
    (D : xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data)
    (n : ℕ) : ℤ :=
  if n ∈ D.sample_nodes then 0 else 1

/-- Two bridges agree on the finite integer samples but are not identical. -/
def exists_distinct_analytic_bridges
    (D : xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data) :
    Prop :=
  ∃ bridgePlus bridgeMinus : ℕ → ℤ,
    bridgePlus ≠ bridgeMinus ∧
      (∀ n, n ∈ D.sample_nodes → bridgePlus n = bridgeMinus n) ∧
      (∀ n,
        bridgePlus n =
          D.base_bridge n +
            D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish
              n) ∧
      (∀ n,
        bridgeMinus n =
          D.base_bridge n -
            D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish
              n)

end xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data

/-- Paper label:
`thm:xi-time-part9xg-finite-integer-moment-samples-do-not-determine-analytic-bridge`. -/
theorem paper_xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge
    (D : xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_data) :
    D.exists_distinct_analytic_bridges := by
  let bridgePlus : ℕ → ℤ := fun n =>
    D.base_bridge n +
      D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish n
  let bridgeMinus : ℕ → ℤ := fun n =>
    D.base_bridge n -
      D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish n
  refine ⟨bridgePlus, bridgeMinus, ?_, ?_, ?_, ?_⟩
  · intro hsame
    have hvalue := congr_fun hsame D.escape_node
    have hvanish :
        D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish
            D.escape_node = 1 := by
      change (if D.escape_node ∈ D.sample_nodes then (0 : ℤ) else 1) = 1
      simp [D.escape_node_not_sample]
    dsimp [bridgePlus, bridgeMinus] at hvalue
    rw [hvanish] at hvalue
    omega
  · intro n hn
    have hvanish :
        D.xi_time_part9xg_finite_integer_moment_samples_do_not_determine_analytic_bridge_vanish
            n = 0 := by
      change (if n ∈ D.sample_nodes then (0 : ℤ) else 1) = 0
      simp [hn]
    dsimp [bridgePlus, bridgeMinus]
    rw [hvanish]
    omega
  · intro n
    rfl
  · intro n
    rfl

end Omega.Zeta
