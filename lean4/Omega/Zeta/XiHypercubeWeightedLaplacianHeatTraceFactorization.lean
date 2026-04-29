import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Powerset
import Mathlib.Tactic
import Omega.Core.WalshFourier

namespace Omega.Zeta

open Omega.Core
open scoped BigOperators

/-- The weighted coordinate-flip Laplacian on the `k`-cube. -/
def xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian
    {k : ℕ} (w : Fin k → ℝ) (f : Word k → ℝ) (ω : Word k) : ℝ :=
  ∑ i : Fin k, w i * (f ω - f (flipBit i ω))

/-- Real-valued Walsh character indexed by the subset `S`. -/
def xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh
    {k : ℕ} (S : Finset (Fin k)) (ω : Word k) : ℝ :=
  (walshChar S ω : ℝ)

/-- The corresponding Laplacian eigenvalue. -/
def xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue
    {k : ℕ} (w : Fin k → ℝ) (S : Finset (Fin k)) : ℝ :=
  2 * ∑ i ∈ S, w i

/-- Heat-trace subset sum for the weighted coordinate-flip Laplacian. -/
noncomputable def xi_hypercube_weighted_laplacian_heat_trace_factorization_heatTrace
    {k : ℕ} (w : Fin k → ℝ) (t : ℝ) : ℝ :=
  ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
    Real.exp (-t * xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S)

private lemma xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh_flip_mem
    {k : ℕ} {S : Finset (Fin k)} {i : Fin k} (hi : i ∈ S) (ω : Word k) :
    xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S (flipBit i ω) =
      -xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
  unfold xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh
  exact_mod_cast walshChar_flipBit_of_mem hi ω

private lemma xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh_flip_not_mem
    {k : ℕ} {S : Finset (Fin k)} {i : Fin k} (hi : i ∉ S) (ω : Word k) :
    xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S (flipBit i ω) =
      xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
  unfold xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh Omega.Core.walshChar
  refine congrArg (fun z : ℤ => (z : ℝ)) ?_
  refine Finset.prod_congr rfl ?_
  intro j hj
  have hji : j ≠ i := by
    intro h
    exact hi (h ▸ hj)
  simp [flipBit_apply_ne, hji]

private lemma xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian_walsh
    {k : ℕ} (w : Fin k → ℝ) (S : Finset (Fin k)) (ω : Word k) :
    xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian w
        (xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S) ω =
      xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S *
        xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
  unfold xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian
    xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue
  calc
    ∑ i : Fin k,
        w i *
          (xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω -
            xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S (flipBit i ω))
        =
      ∑ i : Fin k,
        if i ∈ S then
          2 * w i *
            xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω
        else 0 := by
          refine Finset.sum_congr rfl ?_
          intro i hi
          by_cases his : i ∈ S
          · rw [if_pos his,
              xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh_flip_mem his]
            ring
          · rw [if_neg his,
              xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh_flip_not_mem his]
            ring
    _ = ∑ i ∈ S,
          2 * w i * xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
            simp
    _ = (∑ i ∈ S, 2 * w i) *
          xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
            rw [Finset.sum_mul]
    _ = (2 * ∑ i ∈ S, w i) *
          xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω := by
            congr 1
            rw [← Finset.mul_sum]

private lemma xi_hypercube_weighted_laplacian_heat_trace_factorization_exp_eigenvalue
    {k : ℕ} (w : Fin k → ℝ) (t : ℝ) (S : Finset (Fin k)) :
    Real.exp (-t * xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S) =
      ∏ i ∈ S, Real.exp (-2 * t * w i) := by
  calc
    Real.exp (-t * xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S)
        = Real.exp (∑ i ∈ S, (-2 * t * w i)) := by
            congr 1
            unfold xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue
            rw [Finset.mul_sum]
            calc
              -t * ∑ i ∈ S, 2 * w i = ∑ i ∈ S, (-t) * (2 * w i) := by rw [Finset.mul_sum]
              _ = ∑ i ∈ S, (-2 * t * w i) := by
                    refine Finset.sum_congr rfl ?_
                    intro i hi
                    ring
              _ = ∑ i ∈ S, (-2 * t * w i) := rfl
    _ = ∏ i ∈ S, Real.exp (-2 * t * w i) := by
          rw [Real.exp_sum]

/-- Paper label: `thm:xi-hypercube-weighted-laplacian-heat-trace-factorization`. The Walsh
characters diagonalize the weighted coordinate-flip Laplacian with eigenvalue
`2 * ∑_{i ∈ S} w_i`, and summing the heat factors over all subsets expands to the product
`∏_i (1 + e^{-2 t w_i})`. -/
theorem paper_xi_hypercube_weighted_laplacian_heat_trace_factorization
    (k : ℕ) (w : Fin k → ℝ) (t : ℝ) :
    (∀ S : Finset (Fin k), ∀ ω : Word k,
      xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian w
          (xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S) ω =
        xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S *
          xi_hypercube_weighted_laplacian_heat_trace_factorization_walsh S ω) ∧
    xi_hypercube_weighted_laplacian_heat_trace_factorization_heatTrace w t =
      ∏ i : Fin k, (1 + Real.exp (-2 * t * w i)) := by
  refine ⟨xi_hypercube_weighted_laplacian_heat_trace_factorization_laplacian_walsh w, ?_⟩
  unfold xi_hypercube_weighted_laplacian_heat_trace_factorization_heatTrace
  calc
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
        Real.exp (-t * xi_hypercube_weighted_laplacian_heat_trace_factorization_eigenvalue w S)
        =
      ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset, ∏ i ∈ S, Real.exp (-2 * t * w i) := by
          refine Finset.sum_congr rfl ?_
          intro S hS
          rw [xi_hypercube_weighted_laplacian_heat_trace_factorization_exp_eigenvalue w t S]
    _ = ∏ i : Fin k, (1 + Real.exp (-2 * t * w i)) := by
          symm
          exact Finset.prod_one_add (s := (Finset.univ : Finset (Fin k)))
            (f := fun i => Real.exp (-2 * t * w i))

end Omega.Zeta
