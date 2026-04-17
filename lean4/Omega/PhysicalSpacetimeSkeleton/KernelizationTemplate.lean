import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate

open scoped BigOperators

/-- Quadratic energy induced by a kernel on a finite superposition. -/
def quadraticEnergy {Visible ι : Type} [Fintype ι] (K : Visible → Visible → ℝ)
    (ψ : ι → Visible) (a : ι → ℝ) : ℝ :=
  ∑ i, ∑ j, a i * a j * K (ψ i) (ψ j)

set_option maxHeartbeats 400000 in
/-- Paper-facing seed: a gauge-invariant positive kernel gives a representative-independent
    quadratic readout and interference form.
    prop:physical-spacetime-kernelization-template -/
theorem paper_physical_spacetime_kernelization_template_seeds
    {Visible : Type} (R : Setoid Visible) (K : Visible → Visible → ℝ)
    (hinv : ∀ {x x' y y'}, R.r x x' → R.r y y' → K x y = K x' y')
    (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → Visible) (a : ι → ℝ),
      0 ≤ quadraticEnergy K ψ a)
    {ι : Type} [Fintype ι] (ψ ψ' : ι → Visible) (a : ι → ℝ)
    (hrep : ∀ i, R.r (ψ i) (ψ' i)) :
    quadraticEnergy K ψ a = quadraticEnergy K ψ' a ∧ 0 ≤ quadraticEnergy K ψ a := by
  constructor
  · unfold quadraticEnergy
    refine Finset.sum_congr rfl ?_
    intro i hi
    refine Finset.sum_congr rfl ?_
    intro j hj
    rw [hinv (hrep i) (hrep j)]
  · exact hpsd ψ a

/-- Wrapper theorem matching the paper-facing package name.
    prop:physical-spacetime-kernelization-template -/
theorem paper_physical_spacetime_kernelization_template_package
    {Visible : Type} (R : Setoid Visible) (K : Visible → Visible → ℝ)
    (hinv : ∀ {x x' y y'}, R.r x x' → R.r y y' → K x y = K x' y')
    (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → Visible) (a : ι → ℝ),
      0 ≤ quadraticEnergy K ψ a)
    {ι : Type} [Fintype ι] (ψ ψ' : ι → Visible) (a : ι → ℝ)
    (hrep : ∀ i, R.r (ψ i) (ψ' i)) :
    quadraticEnergy K ψ a = quadraticEnergy K ψ' a ∧ 0 ≤ quadraticEnergy K ψ a :=
  paper_physical_spacetime_kernelization_template_seeds R K hinv hpsd ψ ψ' a hrep

/-- Paper-facing theorem matching the proposition label used in the physical spacetime chapter.
    prop:physical-spacetime-kernelization-template -/
theorem paper_physical_spacetime_kernelization_template
    {Visible : Type} (R : Setoid Visible) (K : Visible → Visible → ℝ)
    (hinv : ∀ {x x' y y'}, R.r x x' → R.r y y' → K x y = K x' y')
    (hpsd : ∀ {ι : Type} [Fintype ι] (ψ : ι → Visible) (a : ι → ℝ),
      0 ≤ Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate.quadraticEnergy K ψ a)
    {ι : Type} [Fintype ι] (ψ ψ' : ι → Visible) (a : ι → ℝ)
    (hrep : ∀ i, R.r (ψ i) (ψ' i)) :
    Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate.quadraticEnergy K ψ a =
        Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate.quadraticEnergy K ψ' a ∧
      0 ≤ Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate.quadraticEnergy K ψ a := by
  exact paper_physical_spacetime_kernelization_template_package R K hinv hpsd ψ ψ' a hrep

end Omega.PhysicalSpacetimeSkeleton.KernelizationTemplate
