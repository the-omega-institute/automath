import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete Jacobi-model data for the strip quartic criterion. The finite spectrum represents
the eigenvalues of the real symmetric Jacobi matrix, and the two endpoints are the positive
forbidden strip boundary values after folding to the one-interval model. -/
structure xi_time_part28b_strip_jacobi_quartic_psd_data where
  xi_time_part28b_strip_jacobi_quartic_psd_spectrum : Finset ℝ
  xi_time_part28b_strip_jacobi_quartic_psd_left : ℝ
  xi_time_part28b_strip_jacobi_quartic_psd_right : ℝ
  xi_time_part28b_strip_jacobi_quartic_psd_left_le_right :
    xi_time_part28b_strip_jacobi_quartic_psd_left ≤
      xi_time_part28b_strip_jacobi_quartic_psd_right

namespace xi_time_part28b_strip_jacobi_quartic_psd_data

def forbiddenInterval (D : xi_time_part28b_strip_jacobi_quartic_psd_data) (x : ℝ) : Prop :=
  D.xi_time_part28b_strip_jacobi_quartic_psd_left < x ∧
    x < D.xi_time_part28b_strip_jacobi_quartic_psd_right

def quarticValue (D : xi_time_part28b_strip_jacobi_quartic_psd_data) (x : ℝ) : ℝ :=
  (x - D.xi_time_part28b_strip_jacobi_quartic_psd_left) *
    (x - D.xi_time_part28b_strip_jacobi_quartic_psd_right)

def noOfflineZeros (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : Prop :=
  ∀ x ∈ D.xi_time_part28b_strip_jacobi_quartic_psd_spectrum, ¬ D.forbiddenInterval x

def forbiddenRootFree (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : Prop :=
  ∀ x ∈ D.xi_time_part28b_strip_jacobi_quartic_psd_spectrum, ¬ D.forbiddenInterval x

def quarticPSD (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : Prop :=
  ∀ x ∈ D.xi_time_part28b_strip_jacobi_quartic_psd_spectrum, 0 ≤ D.quarticValue x

noncomputable def forbiddenCount (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : ℕ := by
  classical
  exact (D.xi_time_part28b_strip_jacobi_quartic_psd_spectrum.filter fun x =>
    D.forbiddenInterval x).card

noncomputable def negativeInertia (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : ℕ := by
  classical
  exact (D.xi_time_part28b_strip_jacobi_quartic_psd_spectrum.filter fun x =>
    D.quarticValue x < 0).card

def forbiddenCountEqNegativeInertia
    (D : xi_time_part28b_strip_jacobi_quartic_psd_data) : Prop :=
  D.forbiddenCount = D.negativeInertia

lemma quarticValue_neg_iff
    (D : xi_time_part28b_strip_jacobi_quartic_psd_data) (x : ℝ) :
    D.quarticValue x < 0 ↔ D.forbiddenInterval x := by
  constructor
  · intro hneg
    unfold quarticValue at hneg
    unfold forbiddenInterval
    constructor
    · by_contra hle
      have hxle : x ≤ D.xi_time_part28b_strip_jacobi_quartic_psd_left := le_of_not_gt hle
      have hleft : x - D.xi_time_part28b_strip_jacobi_quartic_psd_left ≤ 0 := by
        linarith
      have hright : x - D.xi_time_part28b_strip_jacobi_quartic_psd_right ≤ 0 := by
        linarith [D.xi_time_part28b_strip_jacobi_quartic_psd_left_le_right]
      have hnonneg :
          0 ≤ (x - D.xi_time_part28b_strip_jacobi_quartic_psd_left) *
              (x - D.xi_time_part28b_strip_jacobi_quartic_psd_right) :=
        mul_nonneg_of_nonpos_of_nonpos hleft hright
      linarith
    · by_contra hge
      have hxge :
          D.xi_time_part28b_strip_jacobi_quartic_psd_right ≤ x := le_of_not_gt hge
      have hleft : 0 ≤ x - D.xi_time_part28b_strip_jacobi_quartic_psd_left := by
        linarith [D.xi_time_part28b_strip_jacobi_quartic_psd_left_le_right]
      have hright : 0 ≤ x - D.xi_time_part28b_strip_jacobi_quartic_psd_right := by
        linarith
      have hnonneg :
          0 ≤ (x - D.xi_time_part28b_strip_jacobi_quartic_psd_left) *
              (x - D.xi_time_part28b_strip_jacobi_quartic_psd_right) :=
        mul_nonneg hleft hright
      linarith
  · intro hforb
    unfold forbiddenInterval at hforb
    unfold quarticValue
    have hleft : 0 < x - D.xi_time_part28b_strip_jacobi_quartic_psd_left := by
      linarith [hforb.1]
    have hright : x - D.xi_time_part28b_strip_jacobi_quartic_psd_right < 0 := by
      linarith [hforb.2]
    exact mul_neg_of_pos_of_neg hleft hright

lemma quarticValue_nonneg_iff_not_forbidden
    (D : xi_time_part28b_strip_jacobi_quartic_psd_data) (x : ℝ) :
    0 ≤ D.quarticValue x ↔ ¬ D.forbiddenInterval x := by
  constructor
  · intro hnonneg hforb
    have hneg : D.quarticValue x < 0 := (D.quarticValue_neg_iff x).2 hforb
    linarith
  · intro hnot
    by_contra hlt
    have hneg : D.quarticValue x < 0 := lt_of_not_ge hlt
    exact hnot ((D.quarticValue_neg_iff x).1 hneg)

end xi_time_part28b_strip_jacobi_quartic_psd_data

/-- Paper label: `thm:xi-time-part28b-strip-jacobi-quartic-psd`. In the finite Jacobi
spectrum model, absence of off-line strip zeros is exactly absence of spectral points in the
forbidden interval; the quadratic strip factor is nonnegative on the spectrum exactly off that
interval, and the forbidden count is the negative inertia of the strip factor by filtering the
same finite spectrum. -/
theorem paper_xi_time_part28b_strip_jacobi_quartic_psd
    (D : xi_time_part28b_strip_jacobi_quartic_psd_data) :
    (D.noOfflineZeros ↔ D.forbiddenRootFree) ∧ (D.forbiddenRootFree ↔ D.quarticPSD) ∧
      D.forbiddenCountEqNegativeInertia := by
  classical
  refine ⟨?_, ?_, ?_⟩
  · rfl
  · constructor
    · intro hfree x hx
      exact (D.quarticValue_nonneg_iff_not_forbidden x).2 (hfree x hx)
    · intro hpsd x hx
      exact (D.quarticValue_nonneg_iff_not_forbidden x).1 (hpsd x hx)
  · unfold xi_time_part28b_strip_jacobi_quartic_psd_data.forbiddenCountEqNegativeInertia
    unfold xi_time_part28b_strip_jacobi_quartic_psd_data.forbiddenCount
    unfold xi_time_part28b_strip_jacobi_quartic_psd_data.negativeInertia
    apply congrArg Finset.card
    ext x
    simp [xi_time_part28b_strip_jacobi_quartic_psd_data.quarticValue_neg_iff]

end Omega.Zeta
