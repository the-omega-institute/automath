import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Data.Complex.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic
import Omega.GU.GroupJGPrimeRegisterPhaseBohrDense

namespace Omega.SyncKernelWeighted

noncomputable section

/-- A geometric majorant encoding uniform right-half-plane control for the Möbius--log expansion
away from the branch set. -/
def realInput40MobiusLogMajorant (σ₀ : ℝ) (k : ℕ) : ℝ :=
  Real.exp (-σ₀) ^ k

/-- The dense set of branch heights used for the toy primitive-Dirichlet branch package. -/
def realInput40DenseBranchHeights : Set ℝ :=
  (AddSubgroup.closure {Real.log (2 : ℝ), Real.log (3 : ℝ)} : Set ℝ)

/-- Explicit branch points approaching the imaginary axis from the right. -/
def realInput40BohrBranchPoint (n : ℕ) (y : ℝ) : ℂ :=
  ⟨(1 : ℝ) / (n + 1), y⟩

/-- Package for the dense-branch mechanism: a geometric majorant on the right half-plane, a dense
family of imaginary branch heights, and branch points with arbitrarily small positive real part
and imaginary part arbitrarily close to any prescribed target. -/
def RealInput40PrimedirichletDenseBranch : Prop :=
  (∀ σ₀ > 0, Summable (fun k : ℕ => realInput40MobiusLogMajorant σ₀ k)) ∧
    Dense realInput40DenseBranchHeights ∧
    (∀ t ε : ℝ, 0 < ε →
      ∃ n : ℕ, ∃ y : ℝ, y ∈ realInput40DenseBranchHeights ∧
        |(realInput40BohrBranchPoint n y).re| < ε ∧
        |(realInput40BohrBranchPoint n y).im - t| < ε)

private theorem realInput40MobiusLogMajorant_summable (σ₀ : ℝ) (hσ₀ : 0 < σ₀) :
    Summable (fun k : ℕ => realInput40MobiusLogMajorant σ₀ k) := by
  have hnonneg : 0 ≤ Real.exp (-σ₀) := by positivity
  have hlt : Real.exp (-σ₀) < 1 := by
    simpa using (Real.exp_lt_one_iff.mpr (by linarith : -σ₀ < 0))
  simpa [realInput40MobiusLogMajorant] using summable_geometric_of_lt_one hnonneg hlt

private theorem realInput40DenseBranchHeights_dense :
    Dense realInput40DenseBranchHeights := by
  let D : Omega.GU.GroupJGPrimeRegisterPhaseData := ⟨1, by norm_num⟩
  simpa [realInput40DenseBranchHeights, D, Omega.GU.GroupJGPrimeRegisterPhaseData.phaseImageDense] using
    Omega.GU.paper_group_jg_prime_register_phase_bohr_dense D

private theorem realInput40BohrBranchPoint_re (n : ℕ) (y : ℝ) :
    (realInput40BohrBranchPoint n y).re = (1 : ℝ) / (n + 1) := by
  rfl

private theorem realInput40BohrBranchPoint_im (n : ℕ) (y : ℝ) :
    (realInput40BohrBranchPoint n y).im = y := by
  rfl

private theorem realInput40_dense_branch_near_axis (t ε : ℝ) (hε : 0 < ε) :
    ∃ n : ℕ, ∃ y : ℝ, y ∈ realInput40DenseBranchHeights ∧
      |(realInput40BohrBranchPoint n y).re| < ε ∧
      |(realInput40BohrBranchPoint n y).im - t| < ε := by
  have hDense : Dense realInput40DenseBranchHeights := realInput40DenseBranchHeights_dense
  have htClosure : t ∈ closure realInput40DenseBranchHeights := hDense t
  rcases Metric.mem_closure_iff.1 htClosure ε hε with ⟨y, hy, hyε⟩
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
  refine ⟨n, y, hy, ?_, ?_⟩
  · rw [realInput40BohrBranchPoint_re]
    have hpos : 0 < ((n : ℝ) + 1) := by positivity
    have habs : |((n : ℝ) + 1)|⁻¹ = (((n : ℝ) + 1) : ℝ)⁻¹ := by
      rw [abs_of_pos hpos]
    simpa [one_div, habs] using hn
  · rw [realInput40BohrBranchPoint_im]
    simpa [abs_sub_comm, Real.dist_eq] using hyε

/-- Paper label: `thm:real-input-40-primedirichlet-dense-branch`. -/
theorem paper_real_input_40_primedirichlet_dense_branch :
    RealInput40PrimedirichletDenseBranch := by
  exact ⟨realInput40MobiusLogMajorant_summable, realInput40DenseBranchHeights_dense,
    realInput40_dense_branch_near_axis⟩

end

end Omega.SyncKernelWeighted
