import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.MetallicParetoFrontier

open scoped goldenRatio
open Omega.Folding.MetallicParetoFrontier

namespace Omega.Folding

/-- The explicit scalarized score for the integer candidate `A = 1`. -/
noncomputable def metallicIntegerScoreOne (β : ℝ) : ℝ :=
  Real.log (2 / Real.goldenRatio) - β * (1 / Real.log Real.goldenRatio)

/-- The explicit scalarized score for the integer candidate `A = 2`. -/
noncomputable def metallicIntegerScoreTwo (β : ℝ) : ℝ :=
  Real.log (3 / (1 + Real.sqrt 2)) - β * (2 / Real.log (1 + Real.sqrt 2))

/-- The certificate gap between the two surviving integer candidates. -/
noncomputable def metallicIntegerDeltaK : ℝ :=
  2 / Real.log (1 + Real.sqrt 2) - 1 / Real.log Real.goldenRatio

/-- The unique scalarization threshold separating the integer phases `A = 1` and `A = 2`. -/
noncomputable def beta_ZZ : ℝ :=
  (Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio)) / metallicIntegerDeltaK

/-- The audited sample-penalty specialization `β(N) = log N / N`. -/
noncomputable def samplePenaltyBeta (N : ℕ) : ℝ :=
  Real.log (N : ℝ) / (N : ℝ)

private lemma metallicA_goldenRatio : metallicAOfLambda Real.goldenRatio = 1 := by
  unfold metallicAOfLambda
  have hinv : Real.goldenRatio⁻¹ = -Real.goldenConj := by
    simpa [one_div] using Real.inv_goldenRatio
  nlinarith [hinv, Real.goldenRatio_add_goldenConj]

private lemma metallicA_one_add_sqrt_two : metallicAOfLambda (1 + Real.sqrt 2) = 2 := by
  unfold metallicAOfLambda
  have hne : (1 + Real.sqrt 2 : ℝ) ≠ 0 := by positivity
  have hsq : (Real.sqrt 2) ^ 2 = 2 := by
    rw [Real.sq_sqrt]
    positivity
  field_simp [hne]
  nlinarith

private lemma metallicCertificate_goldenRatio :
    metallicCertificateObjective Real.goldenRatio = 1 / Real.log Real.goldenRatio := by
  calc
    metallicCertificateObjective Real.goldenRatio
        = metallicAOfLambda Real.goldenRatio / Real.log Real.goldenRatio := by
            simp [metallicCertificateObjective, metallicAOfLambda]
    _ = 1 / Real.log Real.goldenRatio := by rw [metallicA_goldenRatio]

private lemma metallicCertificate_one_add_sqrt_two :
    metallicCertificateObjective (1 + Real.sqrt 2) = 2 / Real.log (1 + Real.sqrt 2) := by
  calc
    metallicCertificateObjective (1 + Real.sqrt 2)
        = metallicAOfLambda (1 + Real.sqrt 2) / Real.log (1 + Real.sqrt 2) := by
            simp [metallicCertificateObjective, metallicAOfLambda]
    _ = 2 / Real.log (1 + Real.sqrt 2) := by rw [metallicA_one_add_sqrt_two]

private lemma metallicIntegerDeltaK_pos : 0 < metallicIntegerDeltaK := by
  have hlt : Real.goldenRatio < 1 + Real.sqrt 2 := by
    have hphi_lt_two : Real.goldenRatio < 2 := Real.goldenRatio_lt_two
    have htwo_lt : (2 : ℝ) < 1 + Real.sqrt 2 := by
      have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
        simpa [Real.sqrt_one] using
          (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
      linarith
    exact lt_trans hphi_lt_two htwo_lt
  have hkappa :
      metallicCertificateObjective Real.goldenRatio <
        metallicCertificateObjective (1 + Real.sqrt 2) := by
    exact metallicCertificateObjective_strictMonoOn
      (show Real.goldenRatio ∈ Set.Ioi 1 by exact Real.one_lt_goldenRatio)
      (show 1 + Real.sqrt 2 ∈ Set.Ioi 1 by
        have hone_lt : (1 : ℝ) < Real.sqrt 2 := by
          simpa [Real.sqrt_one] using
            (Real.sqrt_lt_sqrt (show (0 : ℝ) ≤ 1 by positivity) (by norm_num : (1 : ℝ) < 2))
        have hsqrt2_pos : (0 : ℝ) < Real.sqrt 2 := lt_trans zero_lt_one hone_lt
        exact lt_add_of_pos_right 1 hsqrt2_pos)
      hlt
  rw [metallicCertificate_goldenRatio, metallicCertificate_one_add_sqrt_two] at hkappa
  simpa [metallicIntegerDeltaK] using hkappa

private lemma metallicIntegerScore_gap (β : ℝ) :
    metallicIntegerScoreTwo β - metallicIntegerScoreOne β =
      metallicIntegerDeltaK * (beta_ZZ - β) := by
  have hscale :
      Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio) =
        metallicIntegerDeltaK * beta_ZZ := by
    unfold beta_ZZ
    field_simp [metallicIntegerDeltaK_pos.ne']
  calc
    metallicIntegerScoreTwo β - metallicIntegerScoreOne β
        = (Real.log (3 / (1 + Real.sqrt 2)) - Real.log (2 / Real.goldenRatio)) -
            β * metallicIntegerDeltaK := by
              unfold metallicIntegerScoreTwo metallicIntegerScoreOne metallicIntegerDeltaK
              ring
    _ = metallicIntegerDeltaK * beta_ZZ - β * metallicIntegerDeltaK := by rw [hscale]
    _ = metallicIntegerDeltaK * (beta_ZZ - β) := by ring

/-- Paper-facing integer threshold law: once the continuous design space has already reduced the
    integer Pareto set to `{1, 2}`, the scalarization score has a unique threshold `beta_ZZ`
    separating the `A = 2`, tie, and `A = 1` phases. -/
theorem paper_metallic_integer_scalarization_threshold :
    (∀ β : ℝ, metallicIntegerScoreTwo β > metallicIntegerScoreOne β ↔ β < beta_ZZ) ∧
    (∀ β : ℝ, metallicIntegerScoreTwo β = metallicIntegerScoreOne β ↔ β = beta_ZZ) ∧
    (∀ β : ℝ, metallicIntegerScoreTwo β < metallicIntegerScoreOne β ↔ beta_ZZ < β) := by
  refine ⟨?_, ?_, ?_⟩
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : 0 < metallicIntegerScoreTwo β - metallicIntegerScoreOne β := sub_pos.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : 0 < metallicIntegerDeltaK * (beta_ZZ - β) := by
        nlinarith [metallicIntegerDeltaK_pos, h]
      rw [← hgap] at h'
      exact sub_pos.mp h'
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : metallicIntegerScoreTwo β - metallicIntegerScoreOne β = 0 := sub_eq_zero.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : metallicIntegerDeltaK * (beta_ZZ - β) = 0 := by
        rw [h]
        ring
      rw [← hgap] at h'
      exact sub_eq_zero.mp h'
  · intro β
    have hgap := metallicIntegerScore_gap β
    constructor
    · intro h
      have h' : metallicIntegerScoreTwo β - metallicIntegerScoreOne β < 0 := sub_neg.mpr h
      rw [hgap] at h'
      nlinarith [metallicIntegerDeltaK_pos, h']
    · intro h
      have h' : metallicIntegerDeltaK * (beta_ZZ - β) < 0 := by
        nlinarith [metallicIntegerDeltaK_pos, h]
      rw [← hgap] at h'
      exact sub_neg.mp h'

private lemma samplePenaltyBeta_succ_lt (n : ℕ) (hn : 3 ≤ n) :
    samplePenaltyBeta (n + 1) < samplePenaltyBeta n := by
  unfold samplePenaltyBeta
  have hn_pos : 0 < (n : ℝ) := by positivity
  have hn_ne : (n : ℝ) ≠ 0 := by positivity
  have hnp1_ne : (((n + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  have hratio_pos : 0 < (((n + 1 : ℕ) : ℝ) / (n : ℝ)) := by positivity
  have hratio :
      Real.log (((n + 1 : ℕ) : ℝ) / (n : ℝ)) < 1 / (n : ℝ) := by
    have hratio_ne : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ≠ 1 := by
      intro hEq
      have hcast : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) := by
        have := (div_eq_iff hn_ne).mp hEq
        simpa using this
      have hnat : n + 1 = n := by
        exact_mod_cast hcast
      exact Nat.succ_ne_self n hnat
    have h := Real.log_lt_sub_one_of_pos hratio_pos hratio_ne
    have hsimp : (((n + 1 : ℕ) : ℝ) / (n : ℝ)) - 1 = 1 / (n : ℝ) := by
      field_simp [hn_ne]
      norm_num
    rw [hsimp] at h
    exact h
  have hlogdiff :
      Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ) < 1 / (n : ℝ) := by
    rwa [Real.log_div hnp1_ne hn_ne] at hratio
  have hlogn_gt_one : 1 < Real.log (n : ℝ) := by
    have hthree_le : (3 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hexp_lt_n : Real.exp 1 < (n : ℝ) := lt_of_lt_of_le Real.exp_one_lt_three hthree_le
    exact (Real.lt_log_iff_exp_lt hn_pos).2 hexp_lt_n
  have hscaled :
      (n : ℝ) * (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) < 1 := by
    have hmul :
        (n : ℝ) * (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) <
          (n : ℝ) * (1 / (n : ℝ)) := by
      exact mul_lt_mul_of_pos_left hlogdiff hn_pos
    have hsimp : (n : ℝ) * (1 / (n : ℝ)) = 1 := by
      field_simp [hn_ne]
    rw [hsimp] at hmul
    exact hmul
  have haux : (n : ℝ) * (Real.log (((n + 1 : ℕ) : ℝ)) - Real.log (n : ℝ)) < Real.log (n : ℝ) := by
    linarith
  have haux' :
      (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) - (n : ℝ) * Real.log (n : ℝ) < Real.log (n : ℝ) := by
    simpa [mul_sub] using haux
  have hcross :
      (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) < (((n + 1 : ℕ) : ℝ)) * Real.log (n : ℝ) := by
    have hcross' : (n : ℝ) * Real.log (((n + 1 : ℕ) : ℝ)) <
        (n : ℝ) * Real.log (n : ℝ) + Real.log (n : ℝ) := by
      linarith
    have hmul_add :
        (n : ℝ) * Real.log (n : ℝ) + Real.log (n : ℝ) =
          (((n + 1 : ℕ) : ℝ)) * Real.log (n : ℝ) := by
      norm_num
      ring
    rw [hmul_add] at hcross'
    exact hcross'
  have hnp1_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by positivity
  have hgoal :
      Real.log (((n + 1 : ℕ) : ℝ)) * (n : ℝ) < Real.log (n : ℝ) * (((n + 1 : ℕ) : ℝ)) := by
    simpa [mul_comm] using hcross
  exact (div_lt_div_iff₀ hnp1_pos hn_pos).2 hgoal

private lemma samplePenaltyBeta_antitone {m n : ℕ} (hm : 3 ≤ m) (hmn : m ≤ n) :
    samplePenaltyBeta n ≤ samplePenaltyBeta m := by
  rcases Nat.exists_eq_add_of_le hmn with ⟨k, rfl⟩
  induction k with
  | zero =>
      simp
  | succ k ih =>
      have ih' : samplePenaltyBeta (m + k) ≤ samplePenaltyBeta m := ih (Nat.le_add_right m k)
      have hk3 : 3 ≤ m + k := le_trans hm (Nat.le_add_right m k)
      have hstep : samplePenaltyBeta (m + k + 1) < samplePenaltyBeta (m + k) := by
        simpa [Nat.add_assoc] using samplePenaltyBeta_succ_lt (m + k) hk3
      simpa [Nat.add_assoc] using le_trans (le_of_lt hstep) ih'

/-- Paper-facing discrete integer threshold wrapper: `β(N) = log N / N` is strictly decreasing on
`N ≥ 3`, so any certified bracket `β(189) < beta_ZZ < β(188)` immediately yields the audited split
`N ≤ 188` versus `N ≥ 189` for the two surviving integer candidates. -/
theorem paper_metallic_sample_penalty_integer_threshold_lambertw :
    (∀ N : ℕ, 3 ≤ N → samplePenaltyBeta (N + 1) < samplePenaltyBeta N) ∧
    ((samplePenaltyBeta 189 < beta_ZZ ∧ beta_ZZ < samplePenaltyBeta 188) →
      (∀ N : ℕ, 3 ≤ N → N ≤ 188 →
        metallicIntegerScoreTwo (samplePenaltyBeta N) < metallicIntegerScoreOne (samplePenaltyBeta N))
        ∧
      (∀ N : ℕ, 189 ≤ N →
        metallicIntegerScoreTwo (samplePenaltyBeta N) > metallicIntegerScoreOne (samplePenaltyBeta N))) := by
  refine ⟨samplePenaltyBeta_succ_lt, ?_⟩
  intro hbracket
  rcases paper_metallic_integer_scalarization_threshold with ⟨hgt, _, hlt⟩
  refine ⟨?_, ?_⟩
  · intro N hN hN188
    have h188_le : samplePenaltyBeta 188 ≤ samplePenaltyBeta N :=
      samplePenaltyBeta_antitone hN hN188
    have hbeta : beta_ZZ < samplePenaltyBeta N := lt_of_lt_of_le hbracket.2 h188_le
    exact (hlt (samplePenaltyBeta N)).2 hbeta
  · intro N h189
    have hN_le : samplePenaltyBeta N ≤ samplePenaltyBeta 189 :=
      samplePenaltyBeta_antitone (by norm_num) h189
    have hbeta : samplePenaltyBeta N < beta_ZZ := lt_of_le_of_lt hN_le hbracket.1
    exact (hgt (samplePenaltyBeta N)).2 hbeta

end Omega.Folding
