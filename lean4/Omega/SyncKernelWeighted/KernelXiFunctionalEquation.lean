import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Real

noncomputable section

/-- The Dirichlet-style `z`-coordinate attached to the scale `λ`. -/
def kernelXiZ (lam s : ℝ) : ℝ :=
  Real.exp (-s * Real.log lam)

/-- The Dirichlet-style `u`-coordinate attached to the scale `λ`. -/
def kernelXiU (lam s : ℝ) : ℝ :=
  Real.exp ((2 * s - 1) * Real.log lam)

/-- The completed one-variable section cut out from the self-dual kernel determinant. -/
def kernelXiSection (Δ : ℝ → ℝ → ℂ) (lam s : ℝ) : ℂ :=
  Δ (kernelXiZ lam s) (kernelXiU lam s)

/-- The matching zeta section obtained by inversion. -/
def kernelXiZetaSection (Δ : ℝ → ℝ → ℂ) (lam s : ℝ) : ℂ :=
  (kernelXiSection Δ lam s)⁻¹

/-- Substituting `z(s) = λ^{-s}` and `u(s) = λ^{2s-1}` into the self-duality identity
`Δ(z,u) = Δ(uz, 1/u)` yields the exact `s ↦ 1 - s` symmetry of the completed section and of its
reciprocal zeta slice.
    prop:kernel-xi-functional-equation -/
theorem paper_kernel_xi_functional_equation
    (Δ : ℝ → ℝ → ℂ) {lam : ℝ} (hlam : 1 < lam)
    (hselfdual : ∀ z u : ℝ, Δ z u = Δ (u * z) (1 / u)) :
    (∀ s : ℝ, kernelXiSection Δ lam s = kernelXiSection Δ lam (1 - s)) ∧
      ∀ s : ℝ, kernelXiZetaSection Δ lam s = kernelXiZetaSection Δ lam (1 - s) := by
  have _ := hlam
  have hxi : ∀ s : ℝ, kernelXiSection Δ lam s = kernelXiSection Δ lam (1 - s) := by
    intro s
    unfold kernelXiSection kernelXiZ kernelXiU
    rw [hselfdual]
    congr 1
    · rw [← Real.exp_add]
      congr 1
      ring
    · rw [one_div, ← Real.exp_neg]
      congr 1
      ring
  refine ⟨hxi, ?_⟩
  intro s
  unfold kernelXiZetaSection
  rw [hxi s]

end

end Omega.SyncKernelWeighted
