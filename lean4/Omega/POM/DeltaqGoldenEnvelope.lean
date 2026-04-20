import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.POM

/-- The spectral-gap exponent `δ_q = log(Λ_q^2 / r_q)` appearing in the collision-kernel envelope.
    prop:pom-deltaq-golden-envelope -/
noncomputable def pomDeltaq (rq Lambdaq : ℕ → ℝ) (q : ℕ) : ℝ :=
  Real.log ((Lambdaq q) ^ 2 / rq q)

/-- If the spectral radius is strictly below the Perron root and the Perron root is bounded by the
golden-ratio envelope `φ^(q/2 + 1)`, then `δ_q < log r_q` and hence `δ_q` inherits the same golden
envelope.
    prop:pom-deltaq-golden-envelope -/
theorem paper_pom_deltaq_golden_envelope
    (rq Lambdaq : ℕ → ℝ)
    (hLambda_pos : ∀ q, 2 ≤ q → 0 < Lambdaq q)
    (hSpectral : ∀ q, 2 ≤ q → Lambdaq q < rq q)
    (hRqEnvelope : ∀ q, 2 ≤ q → rq q ≤ Real.goldenRatio ^ ((q : ℝ) / 2 + 1)) :
    (∀ q, 2 ≤ q → pomDeltaq rq Lambdaq q < Real.log (rq q)) ∧
      (∀ q, 2 ≤ q → Real.log (rq q) ≤ (((q : ℝ) / 2) + 1) * Real.log Real.goldenRatio) ∧
      (∀ q, 2 ≤ q → pomDeltaq rq Lambdaq q ≤ (((q : ℝ) / 2) + 1) * Real.log Real.goldenRatio) := by
  refine ⟨?_, ?_, ?_⟩
  · intro q hq
    dsimp [pomDeltaq]
    have hLambdaq_pos : 0 < Lambdaq q := hLambda_pos q hq
    have hrq_pos : 0 < rq q := lt_trans hLambdaq_pos (hSpectral q hq)
    have hratio_pos : 0 < (Lambdaq q) ^ 2 / rq q := by
      exact div_pos (sq_pos_of_pos hLambdaq_pos) hrq_pos
    have hratio_lt : (Lambdaq q) ^ 2 / rq q < rq q := by
      have hrq_ne : rq q ≠ 0 := ne_of_gt hrq_pos
      field_simp [hrq_ne]
      nlinarith [hSpectral q hq]
    exact Real.log_lt_log hratio_pos hratio_lt
  · intro q hq
    have hLambdaq_pos : 0 < Lambdaq q := hLambda_pos q hq
    have hrq_pos : 0 < rq q := lt_trans hLambdaq_pos (hSpectral q hq)
    have hlog_le :
        Real.log (rq q) ≤ Real.log (Real.goldenRatio ^ ((q : ℝ) / 2 + 1)) :=
      Real.log_le_log hrq_pos (hRqEnvelope q hq)
    simpa [Real.log_rpow Real.goldenRatio_pos] using hlog_le
  · intro q hq
    have hδ : pomDeltaq rq Lambdaq q < Real.log (rq q) := by
      dsimp [pomDeltaq]
      have hLambdaq_pos : 0 < Lambdaq q := hLambda_pos q hq
      have hrq_pos : 0 < rq q := lt_trans hLambdaq_pos (hSpectral q hq)
      have hratio_pos : 0 < (Lambdaq q) ^ 2 / rq q := by
        exact div_pos (sq_pos_of_pos hLambdaq_pos) hrq_pos
      have hratio_lt : (Lambdaq q) ^ 2 / rq q < rq q := by
        have hrq_ne : rq q ≠ 0 := ne_of_gt hrq_pos
        field_simp [hrq_ne]
        nlinarith [hSpectral q hq]
      exact Real.log_lt_log hratio_pos hratio_lt
    have hlog :
        Real.log (rq q) ≤ (((q : ℝ) / 2) + 1) * Real.log Real.goldenRatio := by
      have hLambdaq_pos : 0 < Lambdaq q := hLambda_pos q hq
      have hrq_pos : 0 < rq q := lt_trans hLambdaq_pos (hSpectral q hq)
      have hlog_le :
          Real.log (rq q) ≤ Real.log (Real.goldenRatio ^ ((q : ℝ) / 2 + 1)) :=
        Real.log_le_log hrq_pos (hRqEnvelope q hq)
      simpa [Real.log_rpow Real.goldenRatio_pos] using hlog_le
    exact le_trans hδ.le hlog

end Omega.POM
