import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic
import Omega.Zeta.XiHellingerKernelFourierSech2

namespace Omega.Zeta

/-- Finite Gram matrix built from the chapter-local Hellinger kernel surrogate. -/
noncomputable def xi_hellinger_gram_first_variation_equilibrium_gram {kappa : Nat}
    (s : Fin kappa → ℝ) : Matrix (Fin kappa) (Fin kappa) ℝ :=
  fun i j => xiHellingerKernelFourierDensity |s i - s j|

/-- Odd force kernel obtained by multiplying the even Hellinger Gram kernel by the gap. -/
noncomputable def xi_hellinger_gram_first_variation_equilibrium_force (Δ : ℝ) : ℝ :=
  Δ * xiHellingerKernelFourierDensity |Δ|

/-- Concrete first-variation equilibrium package: injectivity keeps all off-diagonal gaps
nonzero, the Gram matrix is translation invariant, and the pairwise force balance is antisymmetric.
-/
def xi_hellinger_gram_first_variation_equilibrium_statement {kappa : Nat}
    (s : Fin kappa → Real) : Prop :=
  (∀ i j, i ≠ j → s i - s j ≠ 0) ∧
    (∀ c : ℝ,
      xi_hellinger_gram_first_variation_equilibrium_gram (fun i => s i + c) =
        xi_hellinger_gram_first_variation_equilibrium_gram s) ∧
    (∀ i j,
      xi_hellinger_gram_first_variation_equilibrium_force (s i - s j) +
        xi_hellinger_gram_first_variation_equilibrium_force (s j - s i) = 0)

theorem paper_xi_hellinger_gram_first_variation_equilibrium {kappa : Nat}
    (s : Fin kappa -> Real) (hs : Function.Injective s) :
    xi_hellinger_gram_first_variation_equilibrium_statement s := by
  refine ⟨?_, ?_, ?_⟩
  · intro i j hij
    exact sub_ne_zero.mpr (hs.ne hij)
  · intro c
    ext i j
    have hgap : (s i + c) - (s j + c) = s i - s j := by ring
    simp [xi_hellinger_gram_first_variation_equilibrium_gram, hgap]
  · intro i j
    have hgap : s j - s i = -(s i - s j) := by ring
    rw [xi_hellinger_gram_first_variation_equilibrium_force,
      xi_hellinger_gram_first_variation_equilibrium_force, hgap, abs_neg]
    ring

end Omega.Zeta
