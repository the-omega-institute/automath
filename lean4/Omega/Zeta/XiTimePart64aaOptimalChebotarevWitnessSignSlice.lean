import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part64aa-optimal-chebotarev-witness-sign-slice`. -/
theorem paper_xi_time_part64aa_optimal_chebotarev_witness_sign_slice {ι : Type*}
    [Fintype ι] (w psi : ι → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hzero : (∑ i, w i * psi i) = 0) :
    (Finset.univ.filter (fun i => 0 < psi i)).sum (fun i => w i * psi i) =
      (1 / 2 : ℝ) * ∑ i, w i * |psi i| := by
  classical
  let P : Finset ι := Finset.univ.filter (fun i => 0 < psi i)
  let N : Finset ι := Finset.univ.filter (fun i => ¬ 0 < psi i)
  have hsplit :
      (∑ i, w i * psi i) =
        P.sum (fun i => w i * psi i) + N.sum (fun i => w i * psi i) := by
    simpa [P, N] using
      (Finset.sum_filter_add_sum_filter_not (s := Finset.univ) (p := fun i => 0 < psi i)
        (f := fun i => w i * psi i)).symm
  have hzero_split :
      P.sum (fun i => w i * psi i) + N.sum (fun i => w i * psi i) = 0 := by
    simpa [hsplit] using hzero
  have habs :
      (∑ i, w i * |psi i|) =
        P.sum (fun i => w i * psi i) - N.sum (fun i => w i * psi i) := by
    calc
      (∑ i, w i * |psi i|)
          = P.sum (fun i => w i * |psi i|) + N.sum (fun i => w i * |psi i|) := by
              simpa [P, N] using
                (Finset.sum_filter_add_sum_filter_not (s := Finset.univ)
                  (p := fun i => 0 < psi i) (f := fun i => w i * |psi i|)).symm
      _ = P.sum (fun i => w i * psi i) + N.sum (fun i => -(w i * psi i)) := by
              congr 1
              · refine Finset.sum_congr rfl ?_
                intro i hi
                have hpos : 0 < psi i := by simpa [P] using hi
                rw [abs_of_pos hpos]
              · refine Finset.sum_congr rfl ?_
                intro i hi
                have hnonpos : psi i ≤ 0 := by
                  exact le_of_not_gt (by simpa [N] using hi)
                have _ : 0 ≤ w i := hw i
                rw [abs_of_nonpos hnonpos]
                ring
      _ = P.sum (fun i => w i * psi i) - N.sum (fun i => w i * psi i) := by
              rw [Finset.sum_neg_distrib]
              ring
  rw [habs]
  linarith

end Omega.Zeta
