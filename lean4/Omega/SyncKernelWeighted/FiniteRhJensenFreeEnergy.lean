import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Omega.SyncKernelWeighted

/-- A concrete normalized free-energy witness is obtained by taking the pointwise Jensen/Mahler
expression itself.
    prop:finite-rh-jensen-free-energy -/
theorem paper_finite_rh_jensen_free_energy (lam : ℝ) (hLam : 1 < lam) (mods : List ℝ) :
    ∃ G : ℝ → ℝ, ∀ σ, G σ = (mods.map fun μ => max 0 (Real.log μ - σ * Real.log lam)).sum := by
  let _ := hLam
  refine ⟨fun σ => (mods.map fun μ => max 0 (Real.log μ - σ * Real.log lam)).sum, ?_⟩
  intro σ
  rfl

end Omega.SyncKernelWeighted
