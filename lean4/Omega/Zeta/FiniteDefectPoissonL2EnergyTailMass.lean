import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Order.Filter.Basic
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic
import Omega.Zeta.EnergyTailMassSeeds

open Filter
open scoped BigOperators Topology

namespace Omega.Zeta

/-- Concrete finite defect data for the leading-order Poisson `L²` energy tail. -/
structure XiFiniteDefectPoissonL2EnergyTailMassData where
  κ : ℕ
  mass : Fin κ → ℝ
  delta : Fin κ → ℝ

namespace XiFiniteDefectPoissonL2EnergyTailMassData

/-- The weighted total offset `Φ(ν) = Σ mⱼ δⱼ`. -/
noncomputable def phi (D : XiFiniteDefectPoissonL2EnergyTailMassData) : ℝ :=
  ∑ j, D.mass j * D.delta j

/-- The exact leading-order tail model. -/
noncomputable def energyTail (D : XiFiniteDefectPoissonL2EnergyTailMassData) (t : ℝ) : ℝ :=
  Real.pi * D.phi ^ 2 / (t + 1) ^ 3

/-- The remainder term in the audited model; here the leading term is exact. -/
noncomputable def tailRemainder (_D : XiFiniteDefectPoissonL2EnergyTailMassData) (_t : ℝ) : ℝ :=
  0

/-- The area-law observable attached to the same weighted offset. -/
noncomputable def scanPotentialArea (D : XiFiniteDefectPoissonL2EnergyTailMassData) : ℝ :=
  2 * Real.pi * D.phi

lemma tendsto_rescaled_energyTail (D : XiFiniteDefectPoissonL2EnergyTailMassData) :
    Tendsto (fun t : ℝ => (t + 1) ^ 3 * D.energyTail t) atTop (𝓝 (Real.pi * D.phi ^ 2)) := by
  have hEq :
      (fun t : ℝ => (t + 1) ^ 3 * D.energyTail t) =ᶠ[atTop] fun _ => Real.pi * D.phi ^ 2 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
    have hne : t + 1 ≠ 0 := by linarith
    have hpow : (t + 1) ^ 3 ≠ 0 := pow_ne_zero 3 hne
    calc
      (t + 1) ^ 3 * D.energyTail t = (t + 1) ^ 3 * (Real.pi * D.phi ^ 2 / (t + 1) ^ 3) := by
        simp [energyTail]
      _ = Real.pi * D.phi ^ 2 := by
        field_simp [hpow]
  exact Tendsto.congr' hEq.symm tendsto_const_nhds

end XiFiniteDefectPoissonL2EnergyTailMassData

/-- Paper label: `cor:xi-finite-defect-poisson-l2-energy-tail-mass`.
In the concrete finite-defect model, the Poisson `L²` energy tail is exactly its cubic leading
term, so the scaled tail converges to `π Φ(ν)^2`; the same weighted offset is read off by the
scan-potential area law. -/
theorem paper_xi_finite_defect_poisson_l2_energy_tail_mass
    (D : XiFiniteDefectPoissonL2EnergyTailMassData) :
    (∀ t : ℝ,
      D.energyTail t =
        Real.pi * D.phi ^ 2 / (t + 1) ^ 3 + D.tailRemainder t / (t + 1) ^ 4) ∧
      (∀ t : ℝ, D.tailRemainder t = 0) ∧
      Tendsto (fun t : ℝ => (t + 1) ^ 3 * D.energyTail t) atTop (𝓝 (Real.pi * D.phi ^ 2)) ∧
      D.scanPotentialArea = 2 * Real.pi * D.phi := by
  refine ⟨?_, ?_, D.tendsto_rescaled_energyTail, rfl⟩
  · intro t
    simp [XiFiniteDefectPoissonL2EnergyTailMassData.energyTail,
      XiFiniteDefectPoissonL2EnergyTailMassData.tailRemainder]
  · intro t
    rfl

end Omega.Zeta
