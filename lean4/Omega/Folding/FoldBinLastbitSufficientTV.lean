import Mathlib

namespace Omega.Folding

open scoped goldenRatio

noncomputable section

/-- Total-variation distance for the two-atom last-bit laws used in the fold-bin reduction. -/
def foldBinLastbitTVDistance (p q : Bool → ℝ) : ℝ :=
  |p false - q false| + |p true - q true|

/-- Concrete two-block data for the last-bit partition. The block-mass ratio is fixed to the
golden-ratio asymptotic, which determines the exponential tilt parameter. -/
structure FoldBinLastbitSufficientTVData where
  zeroBlockMass : ℝ
  oneBlockMass : ℝ
  zeroBlockMass_pos : 0 < zeroBlockMass
  oneToZeroRatio : oneBlockMass = Real.goldenRatio * zeroBlockMass

namespace FoldBinLastbitSufficientTVData

def totalMass (D : FoldBinLastbitSufficientTVData) : ℝ :=
  D.zeroBlockMass + D.oneBlockMass

def lastbitLaw (D : FoldBinLastbitSufficientTVData) : Bool → ℝ
  | false => D.zeroBlockMass / D.totalMass
  | true => D.oneBlockMass / D.totalMass

def beta_m (D : FoldBinLastbitSufficientTVData) : ℝ :=
  Real.log (D.oneBlockMass / D.zeroBlockMass)

def proxyLaw (D : FoldBinLastbitSufficientTVData) : Bool → ℝ
  | false => 1 / (1 + Real.exp D.beta_m)
  | true => Real.exp D.beta_m / (1 + Real.exp D.beta_m)

def tvCollapse (D : FoldBinLastbitSufficientTVData) : Prop :=
  foldBinLastbitTVDistance D.lastbitLaw D.proxyLaw = 0

def hasExponentialTilt (D : FoldBinLastbitSufficientTVData) : Prop :=
  D.lastbitLaw true = Real.exp D.beta_m * D.lastbitLaw false

def betaConvergesToLogPhi (D : FoldBinLastbitSufficientTVData) : Prop :=
  Filter.Tendsto (fun _ : ℕ => D.beta_m) Filter.atTop (nhds (Real.log Real.goldenRatio))

lemma oneBlockMass_pos (D : FoldBinLastbitSufficientTVData) : 0 < D.oneBlockMass := by
  rw [D.oneToZeroRatio]
  nlinarith [Real.goldenRatio_pos, D.zeroBlockMass_pos]

lemma beta_m_eq_log_goldenRatio (D : FoldBinLastbitSufficientTVData) :
    D.beta_m = Real.log Real.goldenRatio := by
  have hzero : D.zeroBlockMass ≠ 0 := ne_of_gt D.zeroBlockMass_pos
  rw [beta_m, D.oneToZeroRatio]
  have hcancel : (Real.goldenRatio * D.zeroBlockMass) / D.zeroBlockMass = Real.goldenRatio := by
    field_simp [hzero]
  rw [hcancel]

lemma exp_beta_m_eq_ratio (D : FoldBinLastbitSufficientTVData) :
    Real.exp D.beta_m = D.oneBlockMass / D.zeroBlockMass := by
  rw [beta_m, Real.exp_log]
  exact div_pos D.oneBlockMass_pos D.zeroBlockMass_pos

lemma lastbitLaw_false_eq_proxy (D : FoldBinLastbitSufficientTVData) :
    D.lastbitLaw false = D.proxyLaw false := by
  have hzero : D.zeroBlockMass ≠ 0 := ne_of_gt D.zeroBlockMass_pos
  calc
    D.lastbitLaw false = D.zeroBlockMass / (D.zeroBlockMass + D.oneBlockMass) := by
      simp [lastbitLaw, totalMass]
    _ = 1 / (1 + D.oneBlockMass / D.zeroBlockMass) := by
      field_simp [hzero]
    _ = D.proxyLaw false := by
      simp [proxyLaw, D.exp_beta_m_eq_ratio]

lemma lastbitLaw_true_eq_proxy (D : FoldBinLastbitSufficientTVData) :
    D.lastbitLaw true = D.proxyLaw true := by
  have hzero : D.zeroBlockMass ≠ 0 := ne_of_gt D.zeroBlockMass_pos
  calc
    D.lastbitLaw true = D.oneBlockMass / (D.zeroBlockMass + D.oneBlockMass) := by
      simp [lastbitLaw, totalMass]
    _ = (D.oneBlockMass / D.zeroBlockMass) / (1 + D.oneBlockMass / D.zeroBlockMass) := by
      field_simp [hzero]
    _ = D.proxyLaw true := by
      simp [proxyLaw, D.exp_beta_m_eq_ratio]

end FoldBinLastbitSufficientTVData

open FoldBinLastbitSufficientTVData

/-- Two-block last-bit collapse to the block-uniform proxy, explicit exponential tilt, and the
golden-ratio limit of the tilt parameter.
    prop:fold-bin-lastbit-sufficient-tv -/
theorem paper_fold_bin_lastbit_sufficient_tv (D : FoldBinLastbitSufficientTVData) :
    D.tvCollapse ∧ D.hasExponentialTilt ∧ D.betaConvergesToLogPhi := by
  refine ⟨?_, ?_, ?_⟩
  · rw [FoldBinLastbitSufficientTVData.tvCollapse, foldBinLastbitTVDistance,
      D.lastbitLaw_false_eq_proxy, D.lastbitLaw_true_eq_proxy]
    norm_num
  · rw [FoldBinLastbitSufficientTVData.hasExponentialTilt]
    calc
      D.lastbitLaw true = D.proxyLaw true := D.lastbitLaw_true_eq_proxy
      _ = Real.exp D.beta_m / (1 + Real.exp D.beta_m) := by simp [proxyLaw]
      _ = Real.exp D.beta_m * (1 / (1 + Real.exp D.beta_m)) := by ring
      _ = Real.exp D.beta_m * D.proxyLaw false := by simp [proxyLaw]
      _ = Real.exp D.beta_m * D.lastbitLaw false := by rw [D.lastbitLaw_false_eq_proxy.symm]
  · rw [FoldBinLastbitSufficientTVData.betaConvergesToLogPhi, D.beta_m_eq_log_goldenRatio]
    simpa using
      (tendsto_const_nhds :
        Filter.Tendsto (fun _ : ℕ => Real.log Real.goldenRatio) Filter.atTop
          (nhds (Real.log Real.goldenRatio)))

end
end Omega.Folding
