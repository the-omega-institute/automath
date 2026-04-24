import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The total escape contribution of a single Euler factor `1 - α z^d`. -/
def xiFiniteEulerFactorEscapeContribution (α : ℝ) : ℝ :=
  Real.log (max |α| |α|⁻¹)

/-- The per-root escape contribution of a single Euler factor `1 - α z^d`. -/
def xiFiniteEulerRootEscapeContribution (α : ℝ) (d : ℕ) : ℝ :=
  xiFiniteEulerFactorEscapeContribution α / d

/-- Total escape for a finite family of Euler factors. -/
def xiFiniteEulerTotalEscape {ι : Type} [Fintype ι] (α : ι → ℝ) : ℝ :=
  ∑ v, xiFiniteEulerFactorEscapeContribution (α v)

/-- Inverse-closure of each local Euler factor alphabet. -/
def xiFiniteEulerInverseClosed {ι : Type} (A : ι → Finset ℝ) : Prop :=
  ∀ v a, a ∈ A v → a⁻¹ ∈ A v

/-- The finite Euler package is self-reciprocal when the total escape is invariant under inversion
and each local alphabet is inverse-closed. -/
def xiFiniteEulerSelfReciprocal {ι : Type} [Fintype ι] (α : ι → ℝ) (A : ι → Finset ℝ) : Prop :=
  xiFiniteEulerTotalEscape (fun v => (α v)⁻¹) = xiFiniteEulerTotalEscape α ∧
    xiFiniteEulerInverseClosed A

/-- Paper label: `cor:xi-finite-euler-polynomial-escape-additivity`.
Each Euler factor contributes exactly `log max(|α|, |α|⁻¹)` to the total escape, the finite-layer
escape is the sum of these one-factor contributions, and inverse-closure packages the
self-reciprocity. -/
theorem paper_xi_finite_euler_polynomial_escape_additivity
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (d : ι → ℕ) (α : ι → ℝ) (A : ι → Finset ℝ)
    (hd : ∀ v, 0 < d v) (hα : ∀ v, α v ≠ 0) (hA : xiFiniteEulerInverseClosed A) :
    (∀ v,
      (d v : ℝ) * xiFiniteEulerRootEscapeContribution (α v) (d v) =
        xiFiniteEulerFactorEscapeContribution (α v)) ∧
    (xiFiniteEulerTotalEscape α = ∑ v, xiFiniteEulerFactorEscapeContribution (α v)) ∧
    xiFiniteEulerSelfReciprocal α A := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    have hdv_ne : (d v : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hd v))
    unfold xiFiniteEulerRootEscapeContribution
    rw [div_eq_mul_inv, ← mul_assoc]
    rw [mul_comm (d v : ℝ) (xiFiniteEulerFactorEscapeContribution (α v))]
    rw [mul_assoc, mul_inv_cancel₀ hdv_ne, mul_one]
  · rfl
  · refine ⟨?_, hA⟩
    unfold xiFiniteEulerTotalEscape
    refine Finset.sum_congr rfl ?_
    intro v hv
    have hαv := hα v
    simp [xiFiniteEulerFactorEscapeContribution, hαv, abs_inv, max_comm]

end

end Omega.Zeta
