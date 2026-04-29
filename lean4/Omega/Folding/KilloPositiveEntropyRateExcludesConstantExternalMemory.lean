import Mathlib.Tactic
import Omega.Folding.KilloVisibleEntropyDensityAreaControl
import Omega.SPG.PrimeRegisterBudgetLowerBound

namespace Omega.Folding

/-- Concrete finite-stage data for the positive-entropy-rate obstruction: visible entropy controls
area density, the boundary area density is dominated by a cycle-rank parameter, and a
prime-register encoder with `requiredRegisters` axes injects the resulting `p^r` states into the
external memory budget. -/
structure killo_positive_entropy_rate_excludes_constant_external_memory_data where
  entropyData : Omega.SPG.GaugeVolumeAreaComplementarityData
  cycleRank : ℕ
  areaDensity_le_cycleRank : entropyData.areaDensity ≤ cycleRank
  p : ℕ
  axisCapacity : ℕ
  requiredRegisters : ℕ
  encode : Fin (p ^ cycleRank) → Fin ((axisCapacity + 1) ^ requiredRegisters)
  encode_injective : Function.Injective encode

namespace killo_positive_entropy_rate_excludes_constant_external_memory_data

/-- The concrete number of external registers used by the encoder. -/
def killo_positive_entropy_rate_excludes_constant_external_memory_required_registers
    (D : killo_positive_entropy_rate_excludes_constant_external_memory_data) : ℕ :=
  D.requiredRegisters

private theorem killo_positive_entropy_rate_excludes_constant_external_memory_register_bound_exists
    (D : killo_positive_entropy_rate_excludes_constant_external_memory_data) :
    ∃ k, D.p ^ D.cycleRank ≤ (D.axisCapacity + 1) ^ k := by
  refine ⟨D.requiredRegisters, ?_⟩
  exact
    Omega.SPG.paper_spg_prime_register_budget_lower_bound D.p D.cycleRank D.requiredRegisters
      D.axisCapacity ⟨D.encode, D.encode_injective⟩

/-- The least register count compatible with the concrete `p^r` boundary-state lower bound. -/
noncomputable def killo_positive_entropy_rate_excludes_constant_external_memory_register_lower_bound
    (D : killo_positive_entropy_rate_excludes_constant_external_memory_data) : ℕ :=
  Nat.find
    (killo_positive_entropy_rate_excludes_constant_external_memory_register_bound_exists D)

end killo_positive_entropy_rate_excludes_constant_external_memory_data

open killo_positive_entropy_rate_excludes_constant_external_memory_data

/-- Paper label: `cor:killo-positive-entropy-rate-excludes-constant-external-memory`. The visible
entropy/area inequality gives the area-density side of the obstruction, the area-to-cycle-rank
comparison upgrades it to a concrete boundary-state exponent, and the prime-register budget lower
bound forces at least the stated number of external registers. -/
theorem paper_killo_positive_entropy_rate_excludes_constant_external_memory
    (D : killo_positive_entropy_rate_excludes_constant_external_memory_data) :
    D.killo_positive_entropy_rate_excludes_constant_external_memory_register_lower_bound ≤
      D.killo_positive_entropy_rate_excludes_constant_external_memory_required_registers := by
  have hEntropyArea := paper_killo_visible_entropy_density_area_control D.entropyData
  have hlog2 : 0 < Real.log 2 := by positivity
  have hEntropyCycle :
      (((D.entropyData.dimension : ℝ) * Real.log 2) - D.entropyData.gaugeDensity) /
          (D.entropyData.dimension : ℝ) ≤
        Real.log 2 * D.cycleRank + 1 / (D.entropyData.dimension : ℝ) := by
    calc
      (((D.entropyData.dimension : ℝ) * Real.log 2) - D.entropyData.gaugeDensity) /
            (D.entropyData.dimension : ℝ)
          ≤ Real.log 2 * D.entropyData.areaDensity + 1 / (D.entropyData.dimension : ℝ) :=
        hEntropyArea
      _ ≤ Real.log 2 * D.cycleRank + 1 / (D.entropyData.dimension : ℝ) := by
        nlinarith [D.areaDensity_le_cycleRank, hlog2]
  have hbudget :
      D.p ^ D.cycleRank ≤
        (D.axisCapacity + 1) ^
          D.killo_positive_entropy_rate_excludes_constant_external_memory_required_registers := by
    exact
      Omega.SPG.paper_spg_prime_register_budget_lower_bound D.p D.cycleRank
        D.killo_positive_entropy_rate_excludes_constant_external_memory_required_registers
        D.axisCapacity ⟨D.encode, D.encode_injective⟩
  exact
    Nat.find_min'
      (killo_positive_entropy_rate_excludes_constant_external_memory_register_bound_exists D)
      hbudget

end Omega.Folding
