import Mathlib.Tactic
import Mathlib.Topology.Basic
import Mathlib.Topology.Algebra.Ring.Basic
import Omega.POM.FiberLeyangKlBernoulliDecomposition

namespace Omega.POM

open scoped BigOperators

/-- The rootwise term in the Lean-side Renyi wrapper: it scales the already-proved KL Bernoulli
contribution by the interpolation parameter `s`. -/
noncomputable def pom_fiber_leyang_renyi_bernoulli_decomposition_root_term
    (α tp tq s : ℝ) : ℝ :=
  s * leyangRootBernoulliKl α tp tq

/-- Lean-side package for the Renyi wrapper: the finite rootwise sum factors through the already
proved KL decomposition, and the `s → 1` specialization is continuous. -/
def pom_fiber_leyang_renyi_bernoulli_decomposition_statement
    (D : POMFiberLeyangKlBernoulliDecompositionData) : Prop :=
  (∀ s : ℝ,
      s * D.conditionalKl =
        ∑ j, pom_fiber_leyang_renyi_bernoulli_decomposition_root_term (D.alpha j) D.tp D.tq s) ∧
    D.klBernoulliDecomposition ∧
    Filter.Tendsto (fun s : ℝ => s * D.conditionalKl) (nhds 1) (nhds D.conditionalKl)

/-- Paper label: `thm:pom-fiber-leyang-renyi-bernoulli-decomposition`. -/
theorem paper_pom_fiber_leyang_renyi_bernoulli_decomposition
    (D : Omega.POM.POMFiberLeyangKlBernoulliDecompositionData) :
    Omega.POM.pom_fiber_leyang_renyi_bernoulli_decomposition_statement D := by
  refine ⟨?_, paper_pom_fiber_leyang_kl_bernoulli_decomposition D, ?_⟩
  · intro s
    calc
      s * D.conditionalKl = s * ∑ j, leyangRootBernoulliKl (D.alpha j) D.tp D.tq := by
        rw [paper_pom_fiber_leyang_kl_bernoulli_decomposition D]
      _ = ∑ j, s * leyangRootBernoulliKl (D.alpha j) D.tp D.tq := by
        rw [Finset.mul_sum]
      _ =
          ∑ j,
            pom_fiber_leyang_renyi_bernoulli_decomposition_root_term (D.alpha j) D.tp D.tq s := by
        simp [pom_fiber_leyang_renyi_bernoulli_decomposition_root_term]
  · let f : ℝ → ℝ := fun s => s * D.conditionalKl
    have hf : Continuous f := continuous_id.mul continuous_const
    simpa [f, one_mul] using hf.tendsto 1

end Omega.POM
