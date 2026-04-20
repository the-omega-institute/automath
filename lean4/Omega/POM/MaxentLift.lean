import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

section MaxentLift

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The explicit microstate space with `d x` points above each macrostate `x`. -/
abbrev FiberMicrostate (d : X → ℕ) := Σ x, Fin (d x)

/-- The fiberwise marginal of a microstate distribution. -/
noncomputable def fiberMarginal (d : X → ℕ) (μ : FiberMicrostate d → ℝ) (x : X) : ℝ :=
  ∑ i : Fin (d x), μ ⟨x, i⟩

/-- The fiber-uniform lift of `π`. -/
noncomputable def fiberUniformLift (d : X → ℕ) (π : X → ℝ) : FiberMicrostate d → ℝ
  | ⟨x, _i⟩ => π x / d x

/-- Fiberwise Shannon entropy written with `Real.negMulLog`. -/
noncomputable def fiberEntropy (d : X → ℕ) (μ : FiberMicrostate d → ℝ) (x : X) : ℝ :=
  ∑ i : Fin (d x), Real.negMulLog (μ ⟨x, i⟩)

/-- Total entropy on the lifted microstate space. -/
noncomputable def liftEntropy (d : X → ℕ) (μ : FiberMicrostate d → ℝ) : ℝ :=
  ∑ x : X, fiberEntropy d μ x

/-- The lift is fiberwise uniform if it is constant along each explicit fiber. -/
def FiberwiseUniform (d : X → ℕ) (μ : FiberMicrostate d → ℝ) : Prop :=
  ∀ x (i j : Fin (d x)), μ ⟨x, i⟩ = μ ⟨x, j⟩

private lemma fiberwise_uniform_eq_uniformLift
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_uniform : FiberwiseUniform d μ) (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) :
    μ = fiberUniformLift d π := by
  funext a
  rcases a with ⟨x, i⟩
  let i0 : Fin (d x) := ⟨0, hd x⟩
  have hi : μ ⟨x, i⟩ = μ ⟨x, i0⟩ := hμ_uniform x i i0
  have hsum :
      fiberMarginal d μ x = (d x : ℝ) * μ ⟨x, i0⟩ := by
    unfold fiberMarginal
    calc
      ∑ j : Fin (d x), μ ⟨x, j⟩ = ∑ _j : Fin (d x), μ ⟨x, i0⟩ := by
        refine Finset.sum_congr rfl ?_
        intro j hj
        exact hμ_uniform x j i0
      _ = (d x : ℝ) * μ ⟨x, i0⟩ := by
        simp
  have hd0 : (d x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hd x))
  have hzero :
      μ ⟨x, i0⟩ = π x / d x := by
    apply (eq_div_iff hd0).2
    calc
      μ ⟨x, i0⟩ * (d x : ℝ) = (d x : ℝ) * μ ⟨x, i0⟩ := by ring
      _ = π x := by rw [← hμ_marginal x, hsum]
  calc
    μ ⟨x, i⟩ = μ ⟨x, i0⟩ := hi
    _ = π x / d x := hzero
    _ = fiberUniformLift d π ⟨x, i⟩ := rfl

private lemma fiber_uniform_entropy_formula
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (x : X) :
    fiberEntropy d (fiberUniformLift d π) x =
      Real.negMulLog (π x) + π x * Real.log (d x) := by
  have hd0 : (d x : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (hd x))
  have hsum :
      fiberEntropy d (fiberUniformLift d π) x = (d x : ℝ) * Real.negMulLog (π x / d x) := by
    simp [fiberEntropy, fiberUniformLift, hd0]
  rw [hsum]
  have hlog :
      Real.negMulLog (π x / d x) =
        Real.negMulLog (π x) / d x + π x * Real.log (d x) / d x := by
    by_cases hπ : π x = 0
    · simp [hπ, hd0]
    · rw [Real.negMulLog, Real.negMulLog]
      have hd_pos : 0 < (d x : ℝ) := by exact_mod_cast hd x
      rw [Real.log_div hπ hd0]
      field_simp [hd0]
      ring
  calc
    (d x : ℝ) * Real.negMulLog (π x / d x)
        = (d x : ℝ) * (Real.negMulLog (π x) / d x + π x * Real.log (d x) / d x) := by rw [hlog]
    _ = (d x : ℝ) * (Real.negMulLog (π x) / d x) +
          (d x : ℝ) * (π x * Real.log (d x) / d x) := by ring
    _ = Real.negMulLog (π x) + π x * Real.log (d x) := by
      field_simp [hd0]

/-- The explicit fiber-uniform lift is uniquely determined by the fiberwise-uniform condition and
the prescribed marginal, and its entropy satisfies the standard decomposition
`H(π̃) = H(π) + E_π[log d(X)]`.
    thm:pom-maxent-lift -/
theorem paper_pom_maxent_lift
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ)
    (μ : FiberMicrostate d → ℝ) (hμ_uniform : FiberwiseUniform d μ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) :
    μ = fiberUniformLift d π ∧
      liftEntropy d μ =
        (∑ x : X, Real.negMulLog (π x)) + ∑ x : X, π x * Real.log (d x) := by
  have hμ : μ = fiberUniformLift d π :=
    fiberwise_uniform_eq_uniformLift d hd π μ hμ_uniform hμ_marginal
  refine ⟨hμ, ?_⟩
  rw [hμ, liftEntropy]
  calc
    ∑ x : X, fiberEntropy d (fiberUniformLift d π) x
        = ∑ x : X, (Real.negMulLog (π x) + π x * Real.log (d x)) := by
            refine Finset.sum_congr rfl ?_
            intro x hx
            exact fiber_uniform_entropy_formula d hd π x
    _ = (∑ x : X, Real.negMulLog (π x)) + ∑ x : X, π x * Real.log (d x) := by
          simpa using
            (Finset.sum_add_distrib
              (s := (Finset.univ : Finset X))
              (f := fun x : X => Real.negMulLog (π x))
              (g := fun x : X => π x * Real.log (d x)))

end MaxentLift

end Omega.POM
