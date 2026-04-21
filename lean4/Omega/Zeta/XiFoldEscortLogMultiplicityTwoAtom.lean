import Mathlib
import Omega.Folding.KilloFoldBinEscortRenyiLogisticGeometry

namespace Omega.Zeta

/-- The two atoms of the escort log-multiplicity limit law. -/
noncomputable def xiFoldEscortLogMultiplicityAtom (b : Bool) : ℝ :=
  if b then -(Real.log Real.goldenRatio) else 0

/-- The limiting two-atom law: mass `θ(q)` on `-log φ` and mass `1 - θ(q)` on `0`. -/
noncomputable def xiFoldEscortLogMultiplicityLaw (q : ℝ) : Bool → ℝ
  | false => 1 - Omega.Folding.killoEscortTheta q
  | true => Omega.Folding.killoEscortTheta q

/-- Moment generating function of the escort log-multiplicity limit law. -/
noncomputable def xiFoldEscortLogMultiplicityMgf (q s : ℝ) : ℝ :=
  ∑ b, xiFoldEscortLogMultiplicityLaw q b * Real.exp (s * xiFoldEscortLogMultiplicityAtom b)

/-- Mean of the two-atom escort log-multiplicity limit law. -/
noncomputable def xiFoldEscortLogMultiplicityMean (q : ℝ) : ℝ :=
  ∑ b, xiFoldEscortLogMultiplicityLaw q b * xiFoldEscortLogMultiplicityAtom b

/-- Variance of the two-atom escort log-multiplicity limit law. -/
noncomputable def xiFoldEscortLogMultiplicityVariance (q : ℝ) : ℝ :=
  ∑ b,
    xiFoldEscortLogMultiplicityLaw q b *
      (xiFoldEscortLogMultiplicityAtom b - xiFoldEscortLogMultiplicityMean q) ^ 2

private lemma xiFoldEscortTheta_closed (q : ℝ) :
    Omega.Folding.killoEscortTheta q = 1 / (1 + Real.goldenRatio ^ (q + 1)) := by
  have hpow : Real.exp ((q + 1) * Real.log Real.goldenRatio) = Real.goldenRatio ^ (q + 1) := by
    rw [show (q + 1) * Real.log Real.goldenRatio = Real.log Real.goldenRatio * (q + 1) by ring]
    symm
    rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
  unfold Omega.Folding.killoEscortTheta
  rw [hpow]

private lemma xiFoldEscortLaw_false (q : ℝ) :
    xiFoldEscortLogMultiplicityLaw q false =
      Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) := by
  rw [show xiFoldEscortLogMultiplicityLaw q false =
      1 - Omega.Folding.killoEscortTheta q by rfl]
  rw [Omega.Folding.killoEscortTheta_one_sub]
  have hpow : Real.exp ((q + 1) * Real.log Real.goldenRatio) = Real.goldenRatio ^ (q + 1) := by
    rw [show (q + 1) * Real.log Real.goldenRatio = Real.log Real.goldenRatio * (q + 1) by ring]
    symm
    rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
  rw [hpow]

private lemma xiFoldEscortLogMultiplicityMgf_closed (q s : ℝ) :
    xiFoldEscortLogMultiplicityMgf q s =
      xiFoldEscortLogMultiplicityLaw q false +
        xiFoldEscortLogMultiplicityLaw q true * Real.goldenRatio ^ (-s) := by
  have hspow : Real.exp (-(s * Real.log Real.goldenRatio)) = Real.goldenRatio ^ (-s) := by
    rw [show -(s * Real.log Real.goldenRatio) = Real.log Real.goldenRatio * (-s) by ring]
    symm
    rw [Real.rpow_def_of_pos Real.goldenRatio_pos]
  unfold xiFoldEscortLogMultiplicityMgf
  simpa [xiFoldEscortLogMultiplicityLaw, xiFoldEscortLogMultiplicityAtom, hspow, add_comm]

private lemma xiFoldEscortLogMultiplicityMean_closed (q : ℝ) :
    xiFoldEscortLogMultiplicityMean q =
      -(Real.log Real.goldenRatio) * Omega.Folding.killoEscortTheta q := by
  unfold xiFoldEscortLogMultiplicityMean
  simp [xiFoldEscortLogMultiplicityLaw, xiFoldEscortLogMultiplicityAtom]
  ring

private lemma xiFoldEscortLogMultiplicityVariance_closed (q : ℝ) :
    xiFoldEscortLogMultiplicityVariance q =
      (Real.log Real.goldenRatio) ^ 2 *
        Omega.Folding.killoEscortTheta q * (1 - Omega.Folding.killoEscortTheta q) := by
  unfold xiFoldEscortLogMultiplicityVariance
  simp [xiFoldEscortLogMultiplicityLaw, xiFoldEscortLogMultiplicityAtom,
    xiFoldEscortLogMultiplicityMean_closed]
  ring

/-- Paper label: `thm:xi-fold-escort-log-multiplicity-two-atom`. The escort last-bit logistic
parameter `θ(q)` determines a two-point law on `{0, -log φ}` whose mgf, mean, and variance are
the direct two-atom evaluations. -/
theorem paper_xi_fold_escort_log_multiplicity_two_atom (q : ℝ) :
    xiFoldEscortLogMultiplicityLaw q false =
      Real.goldenRatio ^ (q + 1) / (1 + Real.goldenRatio ^ (q + 1)) ∧
      xiFoldEscortLogMultiplicityLaw q true =
        1 / (1 + Real.goldenRatio ^ (q + 1)) ∧
      (∀ s : ℝ,
        xiFoldEscortLogMultiplicityMgf q s =
          xiFoldEscortLogMultiplicityLaw q false +
            xiFoldEscortLogMultiplicityLaw q true * Real.goldenRatio ^ (-s)) ∧
      xiFoldEscortLogMultiplicityMean q =
        -(Real.log Real.goldenRatio) * Omega.Folding.killoEscortTheta q ∧
      xiFoldEscortLogMultiplicityVariance q =
        (Real.log Real.goldenRatio) ^ 2 *
          Omega.Folding.killoEscortTheta q * (1 - Omega.Folding.killoEscortTheta q) := by
  refine ⟨xiFoldEscortLaw_false q, xiFoldEscortTheta_closed q, ?_, ?_, ?_⟩
  · intro s
    exact xiFoldEscortLogMultiplicityMgf_closed q s
  · exact xiFoldEscortLogMultiplicityMean_closed q
  · exact xiFoldEscortLogMultiplicityVariance_closed q

end Omega.Zeta
