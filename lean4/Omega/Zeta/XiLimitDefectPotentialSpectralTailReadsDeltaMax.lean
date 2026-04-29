import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- A two-term model for the Fourier-side spectral tail after isolating the top `δ_max` layer. -/
noncomputable def xiDeltaMaxSpectralModel (δmax : ℝ) (G R : ℝ → ℝ) : ℝ → ℝ :=
  fun ξ => Real.exp (-(1 - δmax) * |ξ|) * G ξ + R ξ

/-- Concrete exponential-envelope formulation of the `δ_max` readout: a bounded top-layer
trigonometric factor plus a lower-order remainder gives a global upper envelope and a matching
lower envelope along a sequence where the top layer stays away from zero and the remainder is
small. -/
def xiLimitDefectPotentialSpectralTailReadsDeltaMaxStatement : Prop :=
  ∀ {δmax A c : ℝ} {G R : ℝ → ℝ},
    0 ≤ δmax →
      δmax < 1 →
      0 ≤ A →
      0 < c →
      (∀ ξ, |G ξ| ≤ A) →
      (∀ ξ, |R ξ| ≤ A * Real.exp (-(1 - δmax) * |ξ|)) →
      (∀ N : ℝ, 0 ≤ N →
        ∃ ξ, N ≤ |ξ| ∧ c ≤ |G ξ| ∧
          |R ξ| ≤ (c / 2) * Real.exp (-(1 - δmax) * |ξ|)) →
      ∃ C > 0,
        (∀ ξ, |xiDeltaMaxSpectralModel δmax G R ξ| ≤ C * Real.exp (-(1 - δmax) * |ξ|)) ∧
          ∀ N : ℝ, 0 ≤ N →
            ∃ ξ, N ≤ |ξ| ∧
              (c / 2) * Real.exp (-(1 - δmax) * |ξ|) ≤
                |xiDeltaMaxSpectralModel δmax G R ξ|

/-- Paper-facing wrapper for the `δ_max` spectral-tail readout package.
    cor:xi-limit-defect-potential-spectral-tail-reads-deltamax -/
def paper_xi_limit_defect_potential_spectral_tail_reads_deltamax : Prop :=
  xiLimitDefectPotentialSpectralTailReadsDeltaMaxStatement

theorem paper_xi_limit_defect_potential_spectral_tail_reads_deltamax_proof :
    paper_xi_limit_defect_potential_spectral_tail_reads_deltamax := by
  intro δmax A c G R hδmax_nonneg hδmax_lt_one hA_nonneg hc hG hR hwit
  refine ⟨2 * A + 1, by linarith, ?_, ?_⟩
  · intro ξ
    have hExpNonneg : 0 ≤ Real.exp (-(1 - δmax) * |ξ|) := by positivity
    have hMain :
        |Real.exp (-(1 - δmax) * |ξ|) * G ξ| ≤
          A * Real.exp (-(1 - δmax) * |ξ|) := by
      rw [abs_mul, abs_of_nonneg hExpNonneg]
      calc
        Real.exp (-(1 - δmax) * |ξ|) * |G ξ| ≤
            Real.exp (-(1 - δmax) * |ξ|) * A := by
              gcongr
              exact hG ξ
        _ = A * Real.exp (-(1 - δmax) * |ξ|) := by ring
    have hRem :
        |R ξ| ≤ A * Real.exp (-(1 - δmax) * |ξ|) := hR ξ
    have hTri :
        |xiDeltaMaxSpectralModel δmax G R ξ| ≤
          |Real.exp (-(1 - δmax) * |ξ|) * G ξ| + |R ξ| := by
      refine abs_le.mpr ⟨?_, ?_⟩
      · dsimp [xiDeltaMaxSpectralModel]
        nlinarith [neg_abs_le (Real.exp (-(1 - δmax) * |ξ|) * G ξ), neg_abs_le (R ξ)]
      · dsimp [xiDeltaMaxSpectralModel]
        nlinarith [le_abs_self (Real.exp (-(1 - δmax) * |ξ|) * G ξ), le_abs_self (R ξ)]
    have hTwoA :
        |xiDeltaMaxSpectralModel δmax G R ξ| ≤
          (2 * A) * Real.exp (-(1 - δmax) * |ξ|) := by
      nlinarith
    have hLift :
        (2 * A) * Real.exp (-(1 - δmax) * |ξ|) ≤
          (2 * A + 1) * Real.exp (-(1 - δmax) * |ξ|) := by
      nlinarith [Real.exp_pos (-(1 - δmax) * |ξ|)]
    exact hTwoA.trans hLift
  · intro N hN
    rcases hwit N hN with ⟨ξ, hξN, hGξ, hRξ⟩
    refine ⟨ξ, hξN, ?_⟩
    have hExpNonneg : 0 ≤ Real.exp (-(1 - δmax) * |ξ|) := by positivity
    have hScaled :
        c * Real.exp (-(1 - δmax) * |ξ|) ≤
          |Real.exp (-(1 - δmax) * |ξ|) * G ξ| := by
      rw [abs_mul, abs_of_nonneg hExpNonneg]
      calc
        c * Real.exp (-(1 - δmax) * |ξ|) ≤
            |G ξ| * Real.exp (-(1 - δmax) * |ξ|) := by
              gcongr
        _ = Real.exp (-(1 - δmax) * |ξ|) * |G ξ| := by ring
    have hRev :
        |Real.exp (-(1 - δmax) * |ξ|) * G ξ| ≤
          |xiDeltaMaxSpectralModel δmax G R ξ| + |R ξ| := by
      have hAux :
          |xiDeltaMaxSpectralModel δmax G R ξ + (-R ξ)| ≤
            |xiDeltaMaxSpectralModel δmax G R ξ| + |-R ξ| := by
        refine abs_le.mpr ⟨?_, ?_⟩
        · nlinarith [neg_abs_le (xiDeltaMaxSpectralModel δmax G R ξ), neg_abs_le (-R ξ)]
        · nlinarith [le_abs_self (xiDeltaMaxSpectralModel δmax G R ξ), le_abs_self (-R ξ)]
      simpa [xiDeltaMaxSpectralModel, add_comm, add_left_comm, add_assoc, abs_neg] using hAux
    nlinarith

end Omega.Zeta
