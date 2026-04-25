import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Monotone.Basic
import Mathlib.Tactic
import Omega.Folding.YmAmbiguityShellLowEntropy

namespace Omega.Folding

/-- Concrete data for the ambiguity-spectrum law. The fields model the path-counting identity,
the Perron--Frobenius main coefficient, the spectral gap parameters, and the monotonicity of the
threshold-induced nonnegative adjacency matrices through their Perron radii. -/
structure ym_ambiguity_spectrum_law_data where
  prefixCount : ℕ → ℕ → ℝ
  pathCount : ℕ → ℕ → ℝ
  rho : ℕ → ℝ
  rhoSecond : ℕ → ℝ
  leadingCoeff : ℕ → ℝ
  epsilon : ℕ → ℝ
  secondGap : ℕ → ℝ
  matrixPowerCount : ∀ k n : ℕ, 2 ≤ k → prefixCount k n = pathCount k n
  leadingCoeff_pos : ∀ k : ℕ, 2 ≤ k → 0 < leadingCoeff k
  rho_range : ∀ k : ℕ, 2 ≤ k → 0 < rho k ∧ rho k < 2
  rhoSecond_lt : ∀ k : ℕ, 2 ≤ k → 0 < rhoSecond k → rhoSecond k < rho k
  rho_antitone : ∀ ⦃i j : ℕ⦄, 2 ≤ i → i ≤ j → rho j ≤ rho i
  epsilon_def : ∀ k : ℕ, epsilon k = Real.log 2 - Real.log (rho k)
  secondGap_def : ∀ k : ℕ, secondGap k = Real.log (rho k / rhoSecond k)

/-- Statement package for the ambiguity-spectrum law: the matrix-power path count is the prefix
count, leading PF coefficients are positive, normalized exponents are positive and monotone, and
the second spectral gap is positive when the secondary radius is nonzero. -/
def ym_ambiguity_spectrum_law_statement (D : ym_ambiguity_spectrum_law_data) : Prop :=
  (∀ k n : ℕ, 2 ≤ k → D.prefixCount k n = D.pathCount k n) ∧
    (∀ k : ℕ, 2 ≤ k → 0 < D.leadingCoeff k) ∧
      (∀ k : ℕ, 2 ≤ k → 0 < D.epsilon k) ∧
        (∀ ⦃i j : ℕ⦄, 2 ≤ i → i ≤ j → D.epsilon i ≤ D.epsilon j) ∧
          ∀ k : ℕ, 2 ≤ k → 0 < D.rhoSecond k → 0 < D.secondGap k

/-- Target-prefixed proof of the concrete ambiguity-spectrum law package.
    thm:Ym-ambiguity-spectrum-law -/
theorem paper_ym_ambiguity_spectrum_law
    (prefixCount pathCount : ℕ → ℕ → ℝ)
    (rho rhoSecond leadingCoeff epsilon secondGap : ℕ → ℝ)
    (matrixPowerCount : ∀ k n : ℕ, 2 ≤ k → prefixCount k n = pathCount k n)
    (leadingCoeff_pos : ∀ k : ℕ, 2 ≤ k → 0 < leadingCoeff k)
    (rho_range : ∀ k : ℕ, 2 ≤ k → 0 < rho k ∧ rho k < 2)
    (rhoSecond_lt : ∀ k : ℕ, 2 ≤ k → 0 < rhoSecond k → rhoSecond k < rho k)
    (rho_antitone : ∀ ⦃i j : ℕ⦄, 2 ≤ i → i ≤ j → rho j ≤ rho i)
    (epsilon_def : ∀ k : ℕ, epsilon k = Real.log 2 - Real.log (rho k))
    (secondGap_def : ∀ k : ℕ, secondGap k = Real.log (rho k / rhoSecond k)) :
    ym_ambiguity_spectrum_law_statement
      { prefixCount := prefixCount
        pathCount := pathCount
        rho := rho
        rhoSecond := rhoSecond
        leadingCoeff := leadingCoeff
        epsilon := epsilon
        secondGap := secondGap
        matrixPowerCount := matrixPowerCount
        leadingCoeff_pos := leadingCoeff_pos
        rho_range := rho_range
        rhoSecond_lt := rhoSecond_lt
        rho_antitone := rho_antitone
        epsilon_def := epsilon_def
        secondGap_def := secondGap_def } := by
  refine ⟨matrixPowerCount, leadingCoeff_pos, ?_, ?_, ?_⟩
  · intro k hk
    change 0 < epsilon k
    rw [epsilon_def k]
    have hlog : Real.log (rho k) < Real.log 2 :=
      paper_Ym_ambiguity_shell_low_entropy (rho k) (rho_range k hk)
    linarith
  · intro i j hi hij
    change epsilon i ≤ epsilon j
    rw [epsilon_def i, epsilon_def j]
    have hlog : Real.log (rho j) ≤ Real.log (rho i) :=
      Real.log_le_log ((rho_range j (le_trans hi hij)).1) (rho_antitone hi hij)
    linarith
  · intro k hk hsecond_pos
    change 0 < rhoSecond k at hsecond_pos
    change 0 < secondGap k
    rw [secondGap_def k]
    have hrhoSecond_lt : rhoSecond k < rho k := rhoSecond_lt k hk hsecond_pos
    have hratio_gt_one : 1 < rho k / rhoSecond k := by
      exact (one_lt_div hsecond_pos).2 hrhoSecond_lt
    have hlog_pos : 0 < Real.log (rho k / rhoSecond k) :=
      Real.log_pos hratio_gt_one
    exact hlog_pos

/-- Paper-facing wrapper for the ambiguity-spectrum law: once the matrix-power
counting step and the unique primitive top-SCC Perron--Frobenius package are in
place, the normalized decay law, the second-gap refinement, positivity of the
decay exponents, and the monotonicity chain all follow.
    thm:Ym-ambiguity-spectrum-law -/
theorem paper_Ym_ambiguity_spectrum_law
    (matrixPowerCount uniquePrimitiveTopSCC perronFrobeniusAsymptotic
      normalizedDecayLaw secondGapRefinement : Prop)
    (ρ ε : ℕ → ℝ)
    (hCount : matrixPowerCount)
    (hTop : uniquePrimitiveTopSCC)
    (hPF :
      matrixPowerCount → uniquePrimitiveTopSCC → perronFrobeniusAsymptotic)
    (hDecay : perronFrobeniusAsymptotic → normalizedDecayLaw)
    (hGap : perronFrobeniusAsymptotic → secondGapRefinement)
    (hρrange : ∀ k, 0 < ρ k ∧ ρ k < 2)
    (hρmono : Antitone ρ)
    (hεdef : ∀ k, ε k = Real.log 2 - Real.log (ρ k)) :
    matrixPowerCount ∧ uniquePrimitiveTopSCC ∧ perronFrobeniusAsymptotic ∧
      normalizedDecayLaw ∧ secondGapRefinement ∧ (∀ k, 0 < ε k) ∧ Monotone ε := by
  have hPF' : perronFrobeniusAsymptotic := hPF hCount hTop
  refine ⟨hCount, hTop, hPF', hDecay hPF', hGap hPF', ?_, ?_⟩
  · intro k
    rw [hεdef k]
    have hlog : Real.log (ρ k) < Real.log 2 :=
      paper_Ym_ambiguity_shell_low_entropy (ρ k) (hρrange k)
    linarith
  · intro i j hij
    rw [hεdef i, hεdef j]
    have hlog : Real.log (ρ j) ≤ Real.log (ρ i) :=
      Real.log_le_log (hρrange j).1 (hρmono hij)
    linarith

end Omega.Folding
