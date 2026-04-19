import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete finite-layer data for the affine identity between output entropy and gauge density.
The normalization `μ = d / 2^m` is encoded through the logarithmic rewrite used in the proof, and
the gauge density is given as `κ - 1` plus an explicit exponentially small error term. -/
structure FoldOutputEntropyGaugeAffineIdentityData where
  W : Type
  instFintypeW : Fintype W
  m : ℕ
  mu : W → ℝ
  digitWeight : W → ℝ
  kappa : ℝ
  g : ℝ
  phi : ℝ
  error : ℝ
  hsumMu : ∑ w, mu w = 1
  hlogDigitWeight : ∀ w,
    Real.log (digitWeight w) = (m : ℝ) * Real.log 2 + Real.log (mu w)
  hkappa : kappa = ∑ w, mu w * Real.log (digitWeight w)
  hg : g = kappa - 1 + error
  herror : |error| ≤ (m : ℝ) * (phi / 2) ^ m

attribute [instance] FoldOutputEntropyGaugeAffineIdentityData.instFintypeW

namespace FoldOutputEntropyGaugeAffineIdentityData

/-- Shannon entropy of the normalized output law. -/
noncomputable def entropy (D : FoldOutputEntropyGaugeAffineIdentityData) : ℝ :=
  -∑ w, D.mu w * Real.log (D.mu w)

/-- The exact affine identity `κ_m = m log 2 - H(μ_m)`. -/
def kappaIdentity (D : FoldOutputEntropyGaugeAffineIdentityData) : Prop :=
  D.kappa = (D.m : ℝ) * Real.log 2 - D.entropy

/-- The gauge density differs from the affine expression by an exponentially small error. -/
def gaugeDensityAsymptotic (D : FoldOutputEntropyGaugeAffineIdentityData) : Prop :=
  ∃ err : ℝ,
    |err| ≤ (D.m : ℝ) * (D.phi / 2) ^ D.m ∧
      D.g = (D.m : ℝ) * Real.log 2 - D.entropy - 1 + err

end FoldOutputEntropyGaugeAffineIdentityData

open FoldOutputEntropyGaugeAffineIdentityData

lemma kappa_identity_formula (D : FoldOutputEntropyGaugeAffineIdentityData) :
    D.kappa = (D.m : ℝ) * Real.log 2 - D.entropy := by
  rw [D.hkappa, FoldOutputEntropyGaugeAffineIdentityData.entropy]
  calc
    ∑ w, D.mu w * Real.log (D.digitWeight w)
        = ∑ w, ((D.m : ℝ) * Real.log 2 * D.mu w + D.mu w * Real.log (D.mu w)) := by
            refine Finset.sum_congr rfl ?_
            intro w _
            rw [D.hlogDigitWeight]
            ring
    _ = ((D.m : ℝ) * Real.log 2) * ∑ w, D.mu w + ∑ w, D.mu w * Real.log (D.mu w) := by
          rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    _ = (D.m : ℝ) * Real.log 2 - D.entropy := by
          simp [D.hsumMu, FoldOutputEntropyGaugeAffineIdentityData.entropy]

/-- Rewriting `log d_m` from `μ_m = d_m / 2^m` gives `κ_m = m log 2 - H(μ_m)`, and substituting the
existing gauge asymptotic into that identity yields the affine error form for `g_m`.
    thm:conclusion-fold-output-entropy-gauge-affine-identity -/
theorem paper_conclusion_fold_output_entropy_gauge_affine_identity
    (D : FoldOutputEntropyGaugeAffineIdentityData) :
    D.kappaIdentity ∧ D.gaugeDensityAsymptotic := by
  refine ⟨?_, ?_⟩
  · unfold FoldOutputEntropyGaugeAffineIdentityData.kappaIdentity
    exact kappa_identity_formula D
  · refine ⟨D.error, D.herror, ?_⟩
    calc
      D.g = D.kappa - 1 + D.error := D.hg
      _ = (D.m : ℝ) * Real.log 2 - D.entropy - 1 + D.error := by
            rw [kappa_identity_formula D]
