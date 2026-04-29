import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Omega.SPG

noncomputable section

/-- The vanishing reciprocal factor obtained after dividing the gauge-volume bound by `n + 1`. -/
def hypercube_linear_area_law_density_one_over (n : ℕ) : ℝ :=
  1 / (n + 1 : ℝ)

/-- The normalized image-cardinality correction after dividing by the hypercube dimension. -/
def hypercube_linear_area_law_density_x_term (X : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((X n : ℝ) / (2 : ℝ) ^ n) * hypercube_linear_area_law_density_one_over n

/-- The asymptotic error term obtained by replacing `a n` with its limit `A` and keeping the
vanishing `1 / (n + 1)` and `X_n / ((n + 1) 2^n)` corrections explicit. -/
def hypercube_linear_area_law_density_normalized_error
    (a : ℕ → ℝ) (X : ℕ → ℕ) (A : ℝ) (n : ℕ) : ℝ :=
  (A - a n) * Real.log 2 - hypercube_linear_area_law_density_one_over n +
    hypercube_linear_area_law_density_x_term X n

/-- If the divided Stokes lower bound holds pointwise, the area density tends to `A`, and the
image-cardinality correction vanishes, then the lower bound can be rewritten with an explicit
error term converging to `0`. -/
def hypercube_linear_area_law_density_statement (a g : ℕ → ℝ) (X : ℕ → ℕ) : Prop :=
  ∀ A : ℝ,
    Tendsto a atTop (nhds A) →
    Tendsto (fun n => (X n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0) →
    (∀ n,
      ((1 - a n) * Real.log 2) - hypercube_linear_area_law_density_one_over n +
          hypercube_linear_area_law_density_x_term X n ≤
        g n) →
    Tendsto (hypercube_linear_area_law_density_normalized_error a X A) atTop (nhds 0) ∧
      ∀ n,
        ((1 - A) * Real.log 2) + hypercube_linear_area_law_density_normalized_error a X A n ≤ g n

private lemma hypercube_linear_area_law_density_one_over_tendsto_zero :
    Tendsto hypercube_linear_area_law_density_one_over atTop (nhds 0) := by
  convert ((tendsto_const_div_atTop_nhds_zero_nat (1 : ℝ)).comp (tendsto_add_atTop_nat 1)) using 1
  ext n
  simp [hypercube_linear_area_law_density_one_over, one_div]

private lemma hypercube_linear_area_law_density_x_term_tendsto_zero
    (X : ℕ → ℕ)
    (hX : Tendsto (fun n => (X n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0)) :
    Tendsto (hypercube_linear_area_law_density_x_term X) atTop (nhds 0) := by
  simpa [hypercube_linear_area_law_density_x_term] using
    hX.mul hypercube_linear_area_law_density_one_over_tendsto_zero

private lemma hypercube_linear_area_law_density_normalized_error_tendsto_zero
    (a : ℕ → ℝ) (X : ℕ → ℕ) (A : ℝ)
    (hA : Tendsto a atTop (nhds A))
    (hX : Tendsto (fun n => (X n : ℝ) / (2 : ℝ) ^ n) atTop (nhds 0)) :
    Tendsto (hypercube_linear_area_law_density_normalized_error a X A) atTop (nhds 0) := by
  have hmain :
      Tendsto (fun n => (A - a n) * Real.log 2) atTop (nhds 0) := by
    have hsub : Tendsto (fun n => A - a n) atTop (nhds 0) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℕ => A) atTop (nhds A))).sub hA
    simpa [zero_mul] using hsub.mul tendsto_const_nhds
  have hrest :
      Tendsto
        (fun n =>
          -hypercube_linear_area_law_density_one_over n +
            hypercube_linear_area_law_density_x_term X n)
        atTop (nhds 0) := by
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using
      hypercube_linear_area_law_density_x_term_tendsto_zero X hX |>.add
        hypercube_linear_area_law_density_one_over_tendsto_zero.neg
  have hadd :
      Tendsto
        (fun n =>
          (A - a n) * Real.log 2 +
            (-hypercube_linear_area_law_density_one_over n +
              hypercube_linear_area_law_density_x_term X n))
        atTop (nhds 0) := by
    simpa using hmain.add hrest
  convert hadd using 1
  funext n
  unfold hypercube_linear_area_law_density_normalized_error
  ring

/-- Paper label: `cor:hypercube-linear-area-law-density`. -/
theorem paper_hypercube_linear_area_law_density
    (a g : ℕ → ℝ) (X : ℕ → ℕ) : hypercube_linear_area_law_density_statement a g X := by
  intro A hA hX hlower
  refine ⟨hypercube_linear_area_law_density_normalized_error_tendsto_zero a X A hA hX, ?_⟩
  intro n
  have hrewrite :
      ((1 - A) * Real.log 2) + hypercube_linear_area_law_density_normalized_error a X A n =
        ((1 - a n) * Real.log 2) - hypercube_linear_area_law_density_one_over n +
          hypercube_linear_area_law_density_x_term X n := by
    unfold hypercube_linear_area_law_density_normalized_error
    ring
  rw [hrewrite]
  exact hlower n

end

end Omega.SPG
