import Mathlib.Tactic
import Omega.SyncKernelRealInput.RealInputDefectEntropy

namespace Omega.SyncKernelRealInput

open Filter
open Polynomial

open scoped BigOperators

noncomputable section

/-- The sextic factor appearing for the specialization `m = 5`. -/
def real_input_defect_entropy_m5_sextic : Polynomial ℤ :=
  X ^ 6 - X ^ 5 - C 3 * X ^ 4 - C 2 * X ^ 3 - C 2 * X ^ 2 - C 2 * X + 1

lemma real_input_defect_entropy_m5_sextic_eq :
    real_input_defect_entropy_f 5 = real_input_defect_entropy_m5_sextic := by
  let f : Nat → Polynomial ℤ := fun k => (X : Polynomial ℤ) ^ k
  have hsum :
      Finset.sum (Finset.Icc 1 3) f = X + X ^ 2 + X ^ 3 := by
    have hsplit₁ :
        Finset.sum (Finset.Icc 1 3) f = Finset.sum (Finset.Icc 1 2) f + f 3 := by
      simpa [f] using (Finset.sum_Icc_succ_top (f := f) (show 1 ≤ 3 by decide))
    have hsplit₂ :
        Finset.sum (Finset.Icc 1 2) f = Finset.sum (Finset.Icc 1 1) f + f 2 := by
      simpa [f] using (Finset.sum_Icc_succ_top (f := f) (show 1 ≤ 2 by decide))
    calc
      Finset.sum (Finset.Icc 1 3) f = Finset.sum (Finset.Icc 1 2) f + f 3 := hsplit₁
      _ = (Finset.sum (Finset.Icc 1 1) f + f 2) + f 3 := by rw [hsplit₂]
      _ = X + X ^ 2 + X ^ 3 := by simp [f]
  have hsum' :
      Finset.sum (Finset.Icc 1 3) (fun k => (X : Polynomial ℤ) ^ k) = X + X ^ 2 + X ^ 3 := by
    simpa [f] using hsum
  calc
    real_input_defect_entropy_f 5
        = X ^ 6 - X ^ 5 - C 3 * X ^ 4 - C 2 * (X + X ^ 2 + X ^ 3) + 1 := by
            simp [real_input_defect_entropy_f, hsum']
    _ = real_input_defect_entropy_m5_sextic := by
          simp [real_input_defect_entropy_m5_sextic]
          ring

/-- Paper label: `cor:real-input-defect-entropy-m5`. The general defect-entropy theorem at level
`m` specializes at `m = 5`, where the characteristic factor is the displayed sextic and the
Perron/log constants remain the explicit golden-ratio values already packaged in the ambient
construction. -/
theorem paper_real_input_defect_entropy_m5 :
    real_input_defect_entropy_charpoly 5 = (X + 1) * real_input_defect_entropy_m5_sextic ∧
    real_input_defect_entropy_f 5 = real_input_defect_entropy_m5_sextic ∧
    real_input_defect_entropy_perron_root 5 = Real.goldenRatio ^ (2 : ℕ) ∧
    real_input_defect_entropy_value 5 = Real.log (Real.goldenRatio ^ (2 : ℕ)) ∧
    Tendsto real_input_defect_entropy_perron_root atTop (nhds (Real.goldenRatio ^ (2 : ℕ))) := by
  have hbase := paper_real_input_defect_entropy 5
  rcases hbase with ⟨_, hchar, _, _, _, _, hlim⟩
  refine ⟨?_, real_input_defect_entropy_m5_sextic_eq, rfl, rfl, hlim⟩
  rw [hchar, real_input_defect_entropy_m5_sextic_eq]

end

end Omega.SyncKernelRealInput
