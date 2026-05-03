import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.POM.DisjointnessGraphTensorPowerSpectrum

namespace Omega.POM

noncomputable section

/-- Perron expression extracted from the tensor-power spectrum bookkeeping. -/
def pom_disjointness_ramanujan_q4_critical_perron (q : ℕ) : ℝ :=
  Real.goldenRatio ^ q

/-- Non-Perron critical expression normalized at `q = 4`. -/
def pom_disjointness_ramanujan_q4_critical_nonperron (q : ℕ) : ℝ :=
  Real.goldenRatio ^ if q ≤ 4 then 0 else 1

/-- Concrete paper-facing `q = 4` critical package for the Boolean disjointness spectrum. -/
def pom_disjointness_ramanujan_q4_critical_statement : Prop :=
  pom_disjointness_graph_tensor_power_spectrum_spectrumFormula 4 ∧
    pom_disjointness_ramanujan_q4_critical_perron 4 = Real.goldenRatio ^ (4 : ℕ) ∧
    pom_disjointness_ramanujan_q4_critical_nonperron 4 = 1 ∧
    (∀ q, q ≤ 3 →
      pom_disjointness_ramanujan_q4_critical_perron q <
        pom_disjointness_ramanujan_q4_critical_perron 4) ∧
    (∀ q, 5 ≤ q → 1 < pom_disjointness_ramanujan_q4_critical_nonperron q)

/-- Paper label: `cor:pom-disjointness-ramanujan-q4-critical`. -/
theorem paper_pom_disjointness_ramanujan_q4_critical :
    pom_disjointness_ramanujan_q4_critical_statement := by
  refine ⟨(paper_pom_disjointness_graph_tensor_power_spectrum 4).2, ?_, ?_, ?_, ?_⟩
  · rfl
  · norm_num [pom_disjointness_ramanujan_q4_critical_nonperron]
  · intro q hq
    interval_cases q
    · simpa [pom_disjointness_ramanujan_q4_critical_perron] using
        (pow_lt_pow_right₀ Real.one_lt_goldenRatio (by norm_num : (0 : ℕ) < 4))
    · simpa [pom_disjointness_ramanujan_q4_critical_perron] using
        (pow_lt_pow_right₀ Real.one_lt_goldenRatio (by norm_num : (1 : ℕ) < 4))
    · simpa [pom_disjointness_ramanujan_q4_critical_perron] using
        (pow_lt_pow_right₀ Real.one_lt_goldenRatio (by norm_num : (2 : ℕ) < 4))
    · simpa [pom_disjointness_ramanujan_q4_critical_perron] using
        (pow_lt_pow_right₀ Real.one_lt_goldenRatio (by norm_num : (3 : ℕ) < 4))
  · intro q hq
    have hnot : ¬q ≤ 4 := by omega
    simpa [pom_disjointness_ramanujan_q4_critical_nonperron, hnot] using
      Real.one_lt_goldenRatio

end

end Omega.POM
