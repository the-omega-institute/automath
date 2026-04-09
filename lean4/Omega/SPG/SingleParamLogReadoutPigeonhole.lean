import Mathlib.Tactic

namespace Omega.SPG.SingleParamLogReadoutPigeonhole

open Finset

/-- Weighted sum over a Boolean mask.
    thm:spg-single-parameter-log-readout-vs-diagonal-multichannel-bifurcation -/
def weightedSum {k : ℕ} (w : Fin k → ℝ) (b : Fin k → Bool) : ℝ :=
  ∑ i, (if b i then w i else 0)

/-- Concrete `k = 1` case: the only two boolean vectors differ by `w 0 = ∑ w`,
    and the bound `∑w / (2^1 - 1) = ∑w` is met with equality.
    thm:spg-single-parameter-log-readout-vs-diagonal-multichannel-bifurcation -/
theorem pigeonhole_k_one (w : Fin 1 → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ b b' : Fin 1 → Bool, b ≠ b' ∧
      |weightedSum w b - weightedSum w b'| ≤ (∑ i, w i) / (2^1 - 1 : ℝ) := by
  refine ⟨fun _ => true, fun _ => false, ?_, ?_⟩
  · intro h
    have := congrFun h 0
    simp at this
  · unfold weightedSum
    simp
    have h0 : 0 ≤ w 0 := (hw 0).le
    rw [abs_of_nonneg h0]
    linarith

/-- Paper package (k=1 concrete instance).
    thm:spg-single-parameter-log-readout-vs-diagonal-multichannel-bifurcation -/
theorem paper_spg_single_parameter_log_readout_pigeonhole_k1
    (w : Fin 1 → ℝ) (hw : ∀ i, 0 < w i) :
    ∃ b b' : Fin 1 → Bool, b ≠ b' ∧
      |weightedSum w b - weightedSum w b'| ≤ (∑ i, w i) / (2^1 - 1 : ℝ) :=
  pigeonhole_k_one w hw

/-- Gödel log-readout concrete `k = 1`: specialized to `w i := log (p i)`.
    thm:spg-single-parameter-log-readout-vs-diagonal-multichannel-bifurcation -/
theorem godel_log_readout_pigeonhole_k1
    (p : Fin 1 → ℝ) (hp : ∀ i, 1 < p i) :
    ∃ b b' : Fin 1 → Bool, b ≠ b' ∧
      |weightedSum (fun i => Real.log (p i)) b -
         weightedSum (fun i => Real.log (p i)) b'|
      ≤ (∑ i, Real.log (p i)) / (2^1 - 1 : ℝ) := by
  apply pigeonhole_k_one
  intro i
  exact Real.log_pos (hp i)

end Omega.SPG.SingleParamLogReadoutPigeonhole
