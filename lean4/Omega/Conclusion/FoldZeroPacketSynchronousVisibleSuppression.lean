import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic

namespace Omega.Conclusion

/-- The collision-excess upper bound forced by a zero packet of size `z`. -/
noncomputable def zeroPacketCollisionUpperBound (M z : ℝ) : ℝ :=
  (M - 1 - z) / M

/-- The max-fiber excess upper bound forced by a zero packet of size `z`. -/
noncomputable def zeroPacketMaxfiberUpperBound (m : ℕ) (M z : ℝ) : ℝ :=
  (2 : ℝ) ^ m * Real.sqrt (zeroPacketCollisionUpperBound M z)

/-- The Shannon-entropy gap upper bound forced by a zero packet of size `z`. -/
noncomputable def zeroPacketEntropyGapUpperBound (M z : ℝ) : ℝ :=
  Real.log (M - z)

/-- The nontrivial Fourier-peak upper bound forced by a zero packet of size `z`. -/
noncomputable def zeroPacketFourierUpperBound (m : ℕ) (M z : ℝ) : ℝ :=
  (2 : ℝ) ^ m * Real.sqrt (M - 1 - z)

private lemma zeroPacketCollisionUpperBound_anti
    {M Fd Zm : ℝ} (hM : 0 < M) (hzero : Fd ≤ Zm) :
    zeroPacketCollisionUpperBound M Zm ≤ zeroPacketCollisionUpperBound M Fd := by
  unfold zeroPacketCollisionUpperBound
  refine div_le_div_of_nonneg_right ?_ hM.le
  linarith

private lemma zeroPacketMaxfiberUpperBound_anti
    {m : ℕ} {M Fd Zm : ℝ} (hM : 0 < M) (hzero : Fd ≤ Zm) :
    zeroPacketMaxfiberUpperBound m M Zm ≤ zeroPacketMaxfiberUpperBound m M Fd := by
  have hcol :
      zeroPacketCollisionUpperBound M Zm ≤ zeroPacketCollisionUpperBound M Fd :=
    zeroPacketCollisionUpperBound_anti hM hzero
  have hsqrt :
      Real.sqrt (zeroPacketCollisionUpperBound M Zm) ≤
        Real.sqrt (zeroPacketCollisionUpperBound M Fd) :=
    Real.sqrt_le_sqrt hcol
  unfold zeroPacketMaxfiberUpperBound
  exact mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (by positivity) _)

private lemma zeroPacketEntropyGapUpperBound_anti
    {M Fd Zm : ℝ} (hzero : Fd ≤ Zm) (hZm : Zm < M) :
    zeroPacketEntropyGapUpperBound M Zm ≤ zeroPacketEntropyGapUpperBound M Fd := by
  unfold zeroPacketEntropyGapUpperBound
  have harg : M - Zm ≤ M - Fd := by linarith
  exact Real.log_le_log (by linarith) harg

private lemma zeroPacketFourierUpperBound_anti
    {m : ℕ} {M Fd Zm : ℝ} (hzero : Fd ≤ Zm) :
    zeroPacketFourierUpperBound m M Zm ≤ zeroPacketFourierUpperBound m M Fd := by
  have hsqrt : Real.sqrt (M - 1 - Zm) ≤ Real.sqrt (M - 1 - Fd) := by
    apply Real.sqrt_le_sqrt
    linarith
  unfold zeroPacketFourierUpperBound
  exact mul_le_mul_of_nonneg_left hsqrt (pow_nonneg (by positivity) _)

/-- Paper label: `thm:conclusion-zero-packet-synchronous-visible-suppression`.
An `F_d` lower bound on the zero packet specializes the standard `|Z_m|`-indexed bounds for the
collision excess, max-fiber excess, Shannon entropy gap, and nontrivial Fourier peak. -/
theorem paper_conclusion_zero_packet_synchronous_visible_suppression
    (m : ℕ) {M Fd Zm collisionExcess maxfiberExcess entropyGap fourierPeak : ℝ}
    (hM : 0 < M) (hzero : Fd ≤ Zm) (hZm : Zm ≤ M - 1)
    (hcollision : collisionExcess ≤ zeroPacketCollisionUpperBound M Zm)
    (hmaxfiber : maxfiberExcess ≤ zeroPacketMaxfiberUpperBound m M Zm)
    (hentropy : entropyGap ≤ zeroPacketEntropyGapUpperBound M Zm)
    (hfourier : fourierPeak ≤ zeroPacketFourierUpperBound m M Zm) :
    collisionExcess ≤ zeroPacketCollisionUpperBound M Fd ∧
      maxfiberExcess ≤ zeroPacketMaxfiberUpperBound m M Fd ∧
      entropyGap ≤ zeroPacketEntropyGapUpperBound M Fd ∧
      fourierPeak ≤ zeroPacketFourierUpperBound m M Fd := by
  refine ⟨hcollision.trans (zeroPacketCollisionUpperBound_anti hM hzero),
    hmaxfiber.trans (zeroPacketMaxfiberUpperBound_anti hM hzero),
    ?_, hfourier.trans (zeroPacketFourierUpperBound_anti hzero)⟩
  have hZm_lt : Zm < M := by linarith
  exact hentropy.trans (zeroPacketEntropyGapUpperBound_anti hzero hZm_lt)

end Omega.Conclusion
