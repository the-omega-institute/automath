import Mathlib.Topology.Order.Real
import Omega.TypedAddressBiaxialCompletion.JensenDefectFiniteization

namespace Omega.TypedAddressBiaxialCompletion

/-- Concrete countable criterion package for the Jensen-defect finiteization interface. The
defect remains monotone as the radius grows, and a concrete increasing sequence of radii tends to
the boundary point `1`, so vanishing on that sequence is enough to recover vanishing at every
radius in `(0,1)`. -/
structure JensenCountableCriterionData extends JensenDefectFiniteizationData where
  defect_monotone :
    ∀ {ρ₁ ρ₂ : ℝ}, 0 < ρ₁ → ρ₂ < 1 → ρ₁ ≤ ρ₂ → defect ρ₁ ≤ defect ρ₂
  rhoSeq : ℕ → ℝ
  rhoSeq_mono : Monotone rhoSeq
  rhoSeq_mem : ∀ n : ℕ, 0 < rhoSeq n ∧ rhoSeq n < 1
  rhoSeq_tendsto : Filter.Tendsto rhoSeq Filter.atTop (nhds 1)
  rhoSeq_covers : ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → ∃ n : ℕ, ρ ≤ rhoSeq n

namespace JensenCountableCriterionData

/-- Chapter-local RH contract: every admissible radius layer is zero-free. -/
def rh (D : JensenCountableCriterionData) : Prop :=
  ∀ {ρ : ℝ}, 0 < ρ → ρ < 1 → D.zeroFree ρ

end JensenCountableCriterionData

open JensenCountableCriterionData

/-- Countable criterion for the Jensen defect: vanishing on a cofinal sequence of radii tending
to `1` is equivalent to vanishing on every radius layer.
    thm:app-jensen-countable-criterion -/
theorem paper_app_jensen_countable_criterion (D : JensenCountableCriterionData) :
    D.rh ↔ ∀ n : ℕ, D.defect (D.rhoSeq n) = 0 := by
  constructor
  · intro hRh n
    have hMem := D.rhoSeq_mem n
    exact (D.semantics (D.rhoSeq n) hMem.1 hMem.2).2.mpr (hRh hMem.1 hMem.2)
  · intro hCount ρ hρ hρ_lt
    rcases D.rhoSeq_covers hρ hρ_lt with ⟨n, hle⟩
    have hMemρ := D.semantics ρ hρ hρ_lt
    have hMemSeq := D.rhoSeq_mem n
    have hdef_le_zero : D.defect ρ ≤ 0 := by
      calc
        D.defect ρ ≤ D.defect (D.rhoSeq n) := D.defect_monotone hρ hMemSeq.2 hle
        _ = 0 := hCount n
    have hdef_eq_zero : D.defect ρ = 0 := le_antisymm hdef_le_zero hMemρ.1
    exact (D.semantics ρ hρ hρ_lt).2.mp hdef_eq_zero

end Omega.TypedAddressBiaxialCompletion
