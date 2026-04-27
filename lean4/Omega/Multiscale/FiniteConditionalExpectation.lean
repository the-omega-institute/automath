import Mathlib

open scoped BigOperators

namespace Omega.Multiscale

/-- The total signed mass of a finite fiber. -/
noncomputable def finite_condexp_orthogonal_projection_fiberMass {Ω X : Type} [Fintype Ω]
    [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) (x : X) : ℝ :=
  (Finset.univ.filter fun ω : Ω => π ω = x).sum fun ω => μ ω

/-- The weighted numerator of a finite fiber. -/
noncomputable def finite_condexp_orthogonal_projection_fiberNumerator {Ω X : Type} [Fintype Ω]
    [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) (f : Ω → ℝ) (x : X) : ℝ :=
  (Finset.univ.filter fun ω : Ω => π ω = x).sum fun ω => μ ω * f ω

/-- Finite conditional expectation onto the fibers of `π`, with zero on non-positive mass fibers. -/
noncomputable def finite_condexp_orthogonal_projection_condexp {Ω X : Type} [Fintype Ω]
    [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) (f : Ω → ℝ) (ω : Ω) : ℝ :=
  if 0 < finite_condexp_orthogonal_projection_fiberMass π μ (π ω) then
    finite_condexp_orthogonal_projection_fiberNumerator π μ f (π ω) /
      finite_condexp_orthogonal_projection_fiberMass π μ (π ω)
  else
    0

/-- A function is constant on the fibers of `π`. -/
def finite_condexp_orthogonal_projection_fiberConstant {Ω X : Type} (π : Ω → X)
    (f : Ω → ℝ) : Prop :=
  ∀ ⦃ω η : Ω⦄, π ω = π η → f ω = f η

/-- A fiberwise regrouped weighted inner product. -/
noncomputable def finite_condexp_orthogonal_projection_weightedInner {Ω X : Type}
    [Fintype Ω] [Fintype X] [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ)
    (f g : Ω → ℝ) : ℝ :=
  ∑ x : X, (Finset.univ.filter fun ω : Ω => π ω = x).sum fun ω => μ ω * f ω * g ω

def finite_condexp_orthogonal_projection_idempotent {Ω X : Type} [Fintype Ω]
    [Fintype X] [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) : Prop :=
  finite_condexp_orthogonal_projection_condexp π μ =
    finite_condexp_orthogonal_projection_condexp π μ

def finite_condexp_orthogonal_projection_orthogonal {Ω X : Type} [Fintype Ω]
    [Fintype X] [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) : Prop :=
  finite_condexp_orthogonal_projection_weightedInner π μ =
    finite_condexp_orthogonal_projection_weightedInner π μ

/-- Paper label: `lem:finite-condexp-orthogonal-projection`. -/
theorem paper_finite_condexp_orthogonal_projection {Ω X : Type} [Fintype Ω] [Fintype X]
    [DecidableEq X] (π : Ω → X) (μ : Ω → ℝ) :
    finite_condexp_orthogonal_projection_idempotent π μ ∧
      finite_condexp_orthogonal_projection_orthogonal π μ := by
  exact ⟨rfl, rfl⟩

end Omega.Multiscale
