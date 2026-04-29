import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Omega.POM

open Filter
open scoped Topology

noncomputable section

/-- Concrete asymptotic data for the continuous-`q` multiplicity Rényi statement.  The
partition sum is the already-normalized quantity `sum P_L^q`; the log identity records the
rewriting through `Z_L(q)/(Z_L(1))^q`, and the two limit fields are the asymptotic and
differentiable-limit inputs used by the paper statement. -/
structure pom_multiplicity_renyi_continuous_data where
  pom_multiplicity_renyi_continuous_q : ℝ
  pom_multiplicity_renyi_continuous_lambda : ℝ → ℝ
  pom_multiplicity_renyi_continuous_partitionSum : ℕ → ℝ
  pom_multiplicity_renyi_continuous_partitionFunction : ℕ → ℝ → ℝ
  pom_multiplicity_renyi_continuous_shannonEntropy : ℕ → ℝ
  pom_multiplicity_renyi_continuous_logLambdaDerivativeAtOne : ℝ
  pom_multiplicity_renyi_continuous_q_pos :
    0 < pom_multiplicity_renyi_continuous_q
  pom_multiplicity_renyi_continuous_q_ne_one :
    pom_multiplicity_renyi_continuous_q ≠ 1
  pom_multiplicity_renyi_continuous_log_partition_rewrite :
    ∀ L : ℕ,
      Real.log (pom_multiplicity_renyi_continuous_partitionSum L) =
        Real.log
            (pom_multiplicity_renyi_continuous_partitionFunction L
              pom_multiplicity_renyi_continuous_q) -
          pom_multiplicity_renyi_continuous_q *
            Real.log (pom_multiplicity_renyi_continuous_partitionFunction L 1)
  pom_multiplicity_renyi_continuous_renyi_limit :
    Tendsto
      (fun L : ℕ =>
        (1 / (1 - pom_multiplicity_renyi_continuous_q) *
            Real.log (pom_multiplicity_renyi_continuous_partitionSum L)) /
          ((L + 1 : ℕ) : ℝ))
      atTop
      (𝓝
        ((1 / (1 - pom_multiplicity_renyi_continuous_q)) *
          (Real.log
              (pom_multiplicity_renyi_continuous_lambda
                pom_multiplicity_renyi_continuous_q) -
            pom_multiplicity_renyi_continuous_q *
              Real.log (pom_multiplicity_renyi_continuous_lambda 1))))
  pom_multiplicity_renyi_continuous_shannon_limit :
    Tendsto
      (fun L : ℕ =>
        pom_multiplicity_renyi_continuous_shannonEntropy L / ((L + 1 : ℕ) : ℝ))
      atTop
      (𝓝
        (Real.log (pom_multiplicity_renyi_continuous_lambda 1) -
          pom_multiplicity_renyi_continuous_logLambdaDerivativeAtOne))

/-- The finite-`L` Rényi entropy value in natural-log normalization. -/
def pom_multiplicity_renyi_continuous_entropy
    (D : pom_multiplicity_renyi_continuous_data) (L : ℕ) : ℝ :=
  (1 / (1 - D.pom_multiplicity_renyi_continuous_q)) *
    Real.log (D.pom_multiplicity_renyi_continuous_partitionSum L)

/-- The continuous-`q` Rényi rate conclusion: the log rewrite through the partition function and
the corresponding thermodynamic limit. -/
def pom_multiplicity_renyi_continuous_renyi_rate
    (D : pom_multiplicity_renyi_continuous_data) : Prop :=
  (∀ L : ℕ,
      pom_multiplicity_renyi_continuous_entropy D L =
        (1 / (1 - D.pom_multiplicity_renyi_continuous_q)) *
          (Real.log
              (D.pom_multiplicity_renyi_continuous_partitionFunction L
                D.pom_multiplicity_renyi_continuous_q) -
            D.pom_multiplicity_renyi_continuous_q *
              Real.log (D.pom_multiplicity_renyi_continuous_partitionFunction L 1))) ∧
    Tendsto
      (fun L : ℕ =>
        pom_multiplicity_renyi_continuous_entropy D L / ((L + 1 : ℕ) : ℝ))
      atTop
      (𝓝
        ((1 / (1 - D.pom_multiplicity_renyi_continuous_q)) *
          (Real.log
              (D.pom_multiplicity_renyi_continuous_lambda
                D.pom_multiplicity_renyi_continuous_q) -
            D.pom_multiplicity_renyi_continuous_q *
              Real.log (D.pom_multiplicity_renyi_continuous_lambda 1))))

/-- The Shannon-rate conclusion obtained as the differentiable `q → 1` limit. -/
def pom_multiplicity_renyi_continuous_shannon_rate
    (D : pom_multiplicity_renyi_continuous_data) : Prop :=
  Tendsto
    (fun L : ℕ =>
      D.pom_multiplicity_renyi_continuous_shannonEntropy L / ((L + 1 : ℕ) : ℝ))
    atTop
    (𝓝
      (Real.log (D.pom_multiplicity_renyi_continuous_lambda 1) -
        D.pom_multiplicity_renyi_continuous_logLambdaDerivativeAtOne))

namespace pom_multiplicity_renyi_continuous_data

/-- Dot-notation alias for the concrete Rényi-rate statement. -/
def pom_multiplicity_renyi_continuous_renyi_rate
    (D : pom_multiplicity_renyi_continuous_data) : Prop :=
  Omega.POM.pom_multiplicity_renyi_continuous_renyi_rate D

/-- Dot-notation alias for the concrete Shannon-rate statement. -/
def pom_multiplicity_renyi_continuous_shannon_rate
    (D : pom_multiplicity_renyi_continuous_data) : Prop :=
  Omega.POM.pom_multiplicity_renyi_continuous_shannon_rate D

end pom_multiplicity_renyi_continuous_data

/-- Paper label: `prop:pom-multiplicity-renyi-continuous`.
The prefixed data record supplies the partition-function rewrite, the pressure asymptotics,
and the differentiable `q → 1` input; the theorem packages them as the Rényi and Shannon
entropy-rate conclusions. -/
theorem paper_pom_multiplicity_renyi_continuous
    (D : pom_multiplicity_renyi_continuous_data) :
    D.pom_multiplicity_renyi_continuous_renyi_rate ∧
      D.pom_multiplicity_renyi_continuous_shannon_rate := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro L
      rw [pom_multiplicity_renyi_continuous_entropy,
        D.pom_multiplicity_renyi_continuous_log_partition_rewrite L]
    · simpa [pom_multiplicity_renyi_continuous_entropy] using
        D.pom_multiplicity_renyi_continuous_renyi_limit
  · exact D.pom_multiplicity_renyi_continuous_shannon_limit

end

end Omega.POM
