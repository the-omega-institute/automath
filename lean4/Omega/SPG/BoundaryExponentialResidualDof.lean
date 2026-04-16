import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Basic
import Mathlib.Tactic

namespace Omega.SPG

/-- The boundary-volume scale `n 2^(n-1)` rewritten on zero-based indices as `(n+1)2^n`. -/
def boundaryExponentialScale (n : ℕ) : ℝ :=
  (n + 1 : ℝ) * (2 : ℝ) ^ n

/-- Chapter-local asymptotic package for the exponential residual-degree-of-freedom statement. The
field `hlogCard` is the affine-fiber cycle-rank rewrite, with `areaDensity` and `residualError`
encoding the main term and the `o(1)` correction. -/
structure BoundaryExponentialResidualDofData where
  p : ℕ
  prime : Fact p.Prime
  a : ℝ
  logCard : ℕ → ℝ
  areaDensity : ℕ → ℝ
  residualError : ℕ → ℝ
  hlogCard :
    ∀ n,
      logCard n =
        (areaDensity n + residualError n) * boundaryExponentialScale n * Real.log p
  hAreaDensity : Filter.Tendsto areaDensity Filter.atTop (nhds a)
  hResidualError : Filter.Tendsto residualError Filter.atTop (nhds 0)

attribute [instance] BoundaryExponentialResidualDofData.prime

/-- If the normalized area density tends to `a` and the residual correction tends to `0`, then the
log-cardinality has asymptotic growth `(a + o(1)) n 2^(n-1) log p`.
    thm:spg-boundary-exponential-residual-dof -/
theorem paper_spg_boundary_exponential_residual_dof
    (h : BoundaryExponentialResidualDofData) :
    ∃ o : ℕ → ℝ,
      Filter.Tendsto o Filter.atTop (nhds 0) ∧
        ∀ n,
          h.logCard n =
            (h.a + o n) * boundaryExponentialScale n * Real.log h.p := by
  refine ⟨fun n ↦ (h.areaDensity n - h.a) + h.residualError n, ?_, ?_⟩
  · have hmain : Filter.Tendsto (fun n ↦ h.areaDensity n - h.a) Filter.atTop (nhds 0) := by
      simpa using h.hAreaDensity.sub
        (tendsto_const_nhds : Filter.Tendsto (fun _ : ℕ => h.a) Filter.atTop (nhds h.a))
    simpa using hmain.add h.hResidualError
  · intro n
    rw [h.hlogCard n]
    ring

end Omega.SPG
