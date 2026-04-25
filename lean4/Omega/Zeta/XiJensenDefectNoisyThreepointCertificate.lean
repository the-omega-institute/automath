import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete finite atomic data for the noisy three-point Jensen-defect certificate. -/
structure xi_jensen_defect_noisy_threepoint_certificate_Data where
  Atom : Type*
  instFintype : Fintype Atom
  instDecidableEq : DecidableEq Atom
  x : ℝ
  h : ℝ
  ε : ℝ
  location : Atom → ℝ
  multiplicity : Atom → ℕ
  exactMinus : ℝ
  exactCenter : ℝ
  exactPlus : ℝ
  noisyMinus : ℝ
  noisyCenter : ℝ
  noisyPlus : ℝ
  h_nonneg : 0 ≤ h
  ε_nonneg : 0 ≤ ε
  noisyMinus_error : |noisyMinus - exactMinus| ≤ ε
  noisyCenter_error : |noisyCenter - exactCenter| ≤ ε
  noisyPlus_error : |noisyPlus - exactPlus| ≤ ε

attribute [instance] xi_jensen_defect_noisy_threepoint_certificate_Data.instFintype
attribute [instance] xi_jensen_defect_noisy_threepoint_certificate_Data.instDecidableEq

namespace xi_jensen_defect_noisy_threepoint_certificate_Data

/-- The exact centered second difference. -/
def exactSecondDifference (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : ℝ :=
  D.exactPlus - 2 * D.exactCenter + D.exactMinus

/-- The observed noisy centered second difference. -/
def noisySecondDifference (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : ℝ :=
  D.noisyPlus - 2 * D.noisyCenter + D.noisyMinus

/-- The finite hat kernel `(h - |x - t|)_+`. -/
def hatKernel (D : xi_jensen_defect_noisy_threepoint_certificate_Data) (t : ℝ) : ℝ :=
  max (D.h - |D.x - t|) 0

/-- The exact hat-kernel second-difference mass in the finite atomic model. -/
def hatSecondDifference (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : ℝ :=
  ∑ i, (D.multiplicity i : ℝ) * D.hatKernel (D.location i)

/-- Three pointwise errors produce the computable `4ε` second-difference error bound. -/
def noisySecondDifferenceErrorBound
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : Prop :=
  |D.noisySecondDifference - D.exactSecondDifference| ≤ 4 * D.ε

/-- If the noisy second difference clears the `4ε` threshold, some atom lies in the open window. -/
def windowAtomCertificate
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : Prop :=
  D.exactSecondDifference = D.hatSecondDifference →
    4 * D.ε < D.noisySecondDifference →
      ∃ i, 0 < D.hatKernel (D.location i)

/-- The same threshold gives a weighted multiplicity lower bound after using
`(h - |x-t|)_+ ≤ h` for each atom. -/
def multiplicityLowerBound
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) : Prop :=
  D.exactSecondDifference = D.hatSecondDifference →
    4 * D.ε < D.noisySecondDifference →
      D.noisySecondDifference - 4 * D.ε ≤
        D.h * ∑ i, (D.multiplicity i : ℝ)

lemma hatKernel_nonneg (D : xi_jensen_defect_noisy_threepoint_certificate_Data) (t : ℝ) :
    0 ≤ D.hatKernel t := by
  simp [hatKernel]

lemma hatKernel_le_h (D : xi_jensen_defect_noisy_threepoint_certificate_Data) (t : ℝ) :
    D.hatKernel t ≤ D.h := by
  unfold hatKernel
  exact max_le (by linarith [abs_nonneg (D.x - t)]) D.h_nonneg

lemma noisySecondDifference_error_bound
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) :
    D.noisySecondDifferenceErrorBound := by
  let ep := D.noisyPlus - D.exactPlus
  let ec := D.noisyCenter - D.exactCenter
  let em := D.noisyMinus - D.exactMinus
  have hrewrite :
      D.noisySecondDifference - D.exactSecondDifference = ep - 2 * ec + em := by
    simp [noisySecondDifference, exactSecondDifference, ep, ec, em]
    ring
  have htri :
      |ep - 2 * ec + em| ≤ |ep| + 2 * |ec| + |em| := by
    calc
      |ep - 2 * ec + em| ≤ |ep - 2 * ec| + |em| := abs_add_le _ _
      _ ≤ |ep| + |2 * ec| + |em| := by
            nlinarith [abs_sub ep (2 * ec)]
      _ = |ep| + 2 * |ec| + |em| := by simp [abs_mul]
  have hp : |ep| ≤ D.ε := by simpa [ep] using D.noisyPlus_error
  have hc : |ec| ≤ D.ε := by simpa [ec] using D.noisyCenter_error
  have hm : |em| ≤ D.ε := by simpa [em] using D.noisyMinus_error
  rw [noisySecondDifferenceErrorBound, hrewrite]
  nlinarith [htri, hp, hc, hm, D.ε_nonneg, abs_nonneg ec]

lemma exactSecondDifference_pos_of_threshold
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data)
    (hthreshold : 4 * D.ε < D.noisySecondDifference) :
    0 < D.exactSecondDifference := by
  have hbound := D.noisySecondDifference_error_bound
  have hle : D.noisySecondDifference - D.exactSecondDifference ≤ 4 * D.ε := by
    exact le_trans (le_abs_self _) hbound
  linarith

lemma windowAtomCertificate_intro
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) :
    D.windowAtomCertificate := by
  intro hexact hthreshold
  have hpos := D.exactSecondDifference_pos_of_threshold hthreshold
  rw [hexact] at hpos
  by_contra hnone
  have hzero : D.hatSecondDifference = 0 := by
    unfold hatSecondDifference
    apply Finset.sum_eq_zero
    intro i hi
    have hhat_nonpos : ¬ 0 < D.hatKernel (D.location i) := by
      intro hhat
      exact hnone ⟨i, hhat⟩
    have hhat_zero : D.hatKernel (D.location i) = 0 := by
      exact le_antisymm (not_lt.mp hhat_nonpos) (D.hatKernel_nonneg _)
    simp [hhat_zero]
  linarith

lemma hatSecondDifference_le_h_mul_totalMultiplicity
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) :
    D.hatSecondDifference ≤ D.h * ∑ i, (D.multiplicity i : ℝ) := by
  unfold hatSecondDifference
  calc
    (∑ i, (D.multiplicity i : ℝ) * D.hatKernel (D.location i))
        ≤ ∑ i, (D.multiplicity i : ℝ) * D.h := by
          apply Finset.sum_le_sum
          intro i hi
          exact mul_le_mul_of_nonneg_left (D.hatKernel_le_h _) (by positivity)
    _ = D.h * ∑ i, (D.multiplicity i : ℝ) := by
          rw [← Finset.sum_mul]
          ring

lemma multiplicityLowerBound_intro
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) :
    D.multiplicityLowerBound := by
  intro hexact hthreshold
  have hbound := D.noisySecondDifference_error_bound
  have hlower : D.noisySecondDifference - 4 * D.ε ≤ D.exactSecondDifference := by
    have hle : D.noisySecondDifference - D.exactSecondDifference ≤ 4 * D.ε :=
      le_trans (le_abs_self _) hbound
    linarith
  have hupper : D.exactSecondDifference ≤ D.h * ∑ i, (D.multiplicity i : ℝ) := by
    rw [hexact]
    exact D.hatSecondDifference_le_h_mul_totalMultiplicity
  exact le_trans hlower hupper

end xi_jensen_defect_noisy_threepoint_certificate_Data

/-- Paper label: `cor:xi-jensen-defect-noisy-threepoint-certificate`. -/
theorem paper_xi_jensen_defect_noisy_threepoint_certificate
    (D : xi_jensen_defect_noisy_threepoint_certificate_Data) :
    D.noisySecondDifferenceErrorBound ∧ D.windowAtomCertificate ∧ D.multiplicityLowerBound := by
  exact ⟨D.noisySecondDifference_error_bound, D.windowAtomCertificate_intro,
    D.multiplicityLowerBound_intro⟩

end Omega.Zeta
