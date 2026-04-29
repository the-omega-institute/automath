import Mathlib.Tactic
import Omega.Zeta.XiToeplitzPsdJetSemialgebraic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- The good layer consists of local jets whose first `N` Verblunsky coefficients all have modulus
strictly less than `1`. -/
def xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer
    (ell : ℕ → ℝ) (N : ℕ) : Prop :=
  ∀ j < N, |xiVerblunskyFromJet ell j| < 1

/-- The `m`th first-failure layer records that the first bad Verblunsky coefficient occurs exactly
at index `m`. -/
def xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer
    (ell : ℕ → ℝ) (N m : ℕ) : Prop :=
  m < N ∧
    1 ≤ |xiVerblunskyFromJet ell m| ∧
      ∀ j < m, |xiVerblunskyFromJet ell j| < 1

/-- The denominator-cleared Toeplitz minor attached to the jet-determined Toeplitz certificate. -/
def xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor
    (D : xi_toeplitz_psd_jet_semialgebraic_data) (m : ℕ) : ℝ :=
  D.clearingDenominator ^ (m + 1) * (xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D).toeplitzDet m

lemma xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_unique
    {ell : ℕ → ℝ} {N m₁ m₂ : ℕ}
    (hm₁ : xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer ell N m₁)
    (hm₂ : xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer ell N m₂) :
    m₁ = m₂ := by
  rcases hm₁ with ⟨_, hm₁bad, hm₁prefix⟩
  rcases hm₂ with ⟨_, hm₂bad, hm₂prefix⟩
  rcases lt_trichotomy m₁ m₂ with hlt | rfl | hgt
  · exact (False.elim <| (not_le_of_gt (hm₂prefix m₁ hlt)) hm₁bad)
  · rfl
  · exact (False.elim <| (not_le_of_gt (hm₁prefix m₂ hgt)) hm₂bad)

lemma xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor_nonneg_iff
    (D : xi_toeplitz_psd_jet_semialgebraic_data) (m : ℕ) :
    0 ≤ xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor D m ↔
      0 ≤ (xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D).toeplitzDet m := by
  constructor
  · intro hCleared
    by_contra hDet
    have hDetNeg :
        (xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D).toeplitzDet m < 0 :=
      lt_of_not_ge hDet
    have hClearedNeg :
        xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor D m < 0 := by
      unfold xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor
      exact mul_neg_of_pos_of_neg (pow_pos D.clearingDenominator_pos _) hDetNeg
    exact not_lt_of_ge hCleared hClearedNeg
  · intro hDet
    unfold xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor
    exact mul_nonneg (pow_nonneg (le_of_lt D.clearingDenominator_pos) _) hDet

/-- Concrete paper-facing stratification package for Toeplitz failure read from the local jet: the
good layer and first-failure layers are disjoint, every nongood jet lands in a unique
first-failure layer, the good layer gives positive Toeplitz minors, the first bad layer gives the
first nonpositive Toeplitz minor, and clearing the fixed denominator preserves the finite sign
conditions. -/
def xi_local_jet_toeplitz_failure_semialgebraic_stratification_statement (N : ℕ) : Prop :=
  ∀ D : xi_toeplitz_psd_jet_semialgebraic_data, D.N = N →
    let T := xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D
    let good :=
      xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer D.ell N
    let bad :=
      xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer D.ell N
    (good → ∀ m, ¬ bad m) ∧
      (¬ good → ∃! m, bad m) ∧
      (good → ∀ m ≤ N,
        0 < T.toeplitzDet m ∧
          0 ≤ xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor D m) ∧
      (∀ m, bad m →
        T.toeplitzDet (m + 1) ≤ 0 ∧
          xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor D (m + 1) ≤ 0 ∧
          ∀ r < m + 1, 0 < T.toeplitzDet r) ∧
      (∀ m ≤ N,
        0 ≤ xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor D m ↔
          0 ≤ T.toeplitzDet m)

/-- Paper label: `thm:xi-local-jet-toeplitz-failure-semialgebraic-stratification`. -/
theorem paper_xi_local_jet_toeplitz_failure_semialgebraic_stratification
    (N : ℕ) : xi_local_jet_toeplitz_failure_semialgebraic_stratification_statement N := by
  intro D hN
  let T := xi_toeplitz_psd_jet_semialgebraic_toeplitz_data D
  let good :=
    xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer D.ell N
  let bad :=
    xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer D.ell N
  have hLocal :=
    paper_xi_local_jet_determines_finite_cmv_and_toeplitz_certificate D.ell D.coeff
      D.coeff_zero D.coeff_one D.coeff_two D.coeff_zero_pos D.N D.delta0 D.hdelta0
  rcases hLocal with ⟨_, _, _, _, _, hMinControl, hFailureSet⟩
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro hgood m hm
    change xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer D.ell N at hgood
    change xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer D.ell N m
      at hm
    rcases hm with ⟨hmN, hmBad, _⟩
    exact (not_le_of_gt (hgood m hmN)) hmBad
  · intro hnotgood
    change ¬ xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer D.ell N at hnotgood
    change ¬ ∀ j < N, |xiVerblunskyFromJet D.ell j| < 1 at hnotgood
    push_neg at hnotgood
    have hExists :
        ∃ m,
          m < N ∧
            1 ≤ |xiVerblunskyFromJet D.ell m| := by
      rcases hnotgood with ⟨m, hmN, hmBad⟩
      exact ⟨m, hmN, hmBad⟩
    let m := Nat.find hExists
    have hmSpec : m < N ∧ 1 ≤ |xiVerblunskyFromJet D.ell m| := Nat.find_spec hExists
    have hmPrefix : ∀ j < m, |xiVerblunskyFromJet D.ell j| < 1 := by
      intro j hj
      by_contra hjbad
      have hjWitness :
          j < N ∧ 1 ≤ |xiVerblunskyFromJet D.ell j| := by
        refine ⟨lt_trans hj hmSpec.1, le_of_not_gt hjbad⟩
      exact (Nat.not_le_of_lt hj) (Nat.find_min' hExists hjWitness)
    refine ⟨m, ⟨hmSpec.1, hmSpec.2, hmPrefix⟩, ?_⟩
    intro m' hm'
    change xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer D.ell N m'
      at hm'
    exact xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_unique hm' <|
      ⟨hmSpec.1, hmSpec.2, hmPrefix⟩
  · intro hgood m hmN'
    change xi_local_jet_toeplitz_failure_semialgebraic_stratification_good_layer D.ell N at hgood
    have hdetPos : 0 < T.toeplitzDet m := by
      apply T.toeplitzDet_pos_of_prefix_good
      intro j hj
      have hjN : j < N := lt_of_lt_of_le hj hmN'
      have hjD : j < D.N := by simpa [hN] using hjN
      simpa [T, xi_toeplitz_psd_jet_semialgebraic_toeplitz_data, xiToeplitzDetDataFromJet,
        XiToeplitzDetVerblunskyData.alphaAt, xiFiniteCMVPrefix, if_pos hjD] using hgood j hjN
    refine ⟨hdetPos, ?_⟩
    exact (xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor_nonneg_iff
      D m).2 hdetPos.le
  · intro m hm
    change xi_local_jet_toeplitz_failure_semialgebraic_stratification_first_failure_layer D.ell N m
      at hm
    rcases hm with ⟨hmN, hmBad, hmPrefix⟩
    have hMemJet : m + 1 ∈ xiJetFailureSet D.ell D.N := by
      refine ⟨m, ?_, rfl, hmBad⟩
      simpa [hN] using hmN
    have hMem : m + 1 ∈ T.failureSet := by
      simpa [T, xi_toeplitz_psd_jet_semialgebraic_toeplitz_data] using hFailureSet.symm ▸ hMemJet
    have hLeast : IsLeast T.failureSet (m + 1) := by
      refine ⟨hMem, ?_⟩
      intro n hn
      have hnJet : n ∈ xiJetFailureSet D.ell D.N := by
        simpa [T, xi_toeplitz_psd_jet_semialgebraic_toeplitz_data] using hFailureSet ▸ hn
      rcases hnJet with ⟨j, hjN, hEq, hjBad⟩
      have hmLeJ : m ≤ j := by
        by_contra hmLeJ
        have hjLtM : j < m := Nat.lt_of_not_ge hmLeJ
        exact (not_le_of_gt (hmPrefix j hjLtM)) hjBad
      omega
    have hControl := hMinControl (m + 1) hLeast
    refine ⟨hControl.1, ?_, ?_⟩
    · unfold xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor
      exact mul_nonpos_of_nonneg_of_nonpos
        (pow_nonneg (le_of_lt D.clearingDenominator_pos) _) hControl.1
    · intro r hr
      exact hControl.2 r hr
  · intro m hmN'
    exact xi_local_jet_toeplitz_failure_semialgebraic_stratification_cleared_minor_nonneg_iff D m

end

end Omega.Zeta
