import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import Omega.OperatorAlgebra.FoldInfoNCEFiniteKMomentFormula

namespace Omega.Folding

private theorem sum_Icc_two_split_top {f : Nat → Real} {b : Nat} (hb : 2 ≤ b) :
    Finset.sum (Finset.Icc 2 b) f = Finset.sum (Finset.Icc 2 (b - 1)) f + f b := by
  have hbpos : 0 < b := Nat.succ_le_iff.mp (le_trans (by decide) hb)
  have hnot_mem :
      b ∉ Finset.Icc 2 (b - 1) := by
    intro hmem
    have hble : b ≤ b - 1 := (Finset.mem_Icc.mp hmem).2
    exact (Nat.not_le_of_lt (Nat.sub_lt hbpos (by decide))) hble
  rw [← Finset.insert_Icc_sub_one_right_eq_Icc (a := 2) (b := b) hb, Finset.sum_insert hnot_mem]
  simp [add_comm]

private theorem loss_spectrum_identifiability_aux (N : Nat) (beta : Nat → Nat → Real)
    (M M' : Nat → Real)
    (hdiag : ∀ K, 2 ≤ K → K ≤ N → beta K K != 0)
    (heq : ∀ K, 2 ≤ K → K ≤ N →
      Finset.sum (Finset.Icc 2 K) (fun q => beta K q * M q) =
        Finset.sum (Finset.Icc 2 K) (fun q => beta K q * M' q)) :
    ∀ q, 2 ≤ q → q ≤ N → M q = M' q := by
  intro q hq hqN
  refine Nat.strong_induction_on q ?_ hq hqN
  intro q ih hq hqN
  have hprefix :
      Finset.sum (Finset.Icc 2 (q - 1)) (fun r => beta q r * M r) =
        Finset.sum (Finset.Icc 2 (q - 1)) (fun r => beta q r * M' r) := by
    refine Finset.sum_congr rfl ?_
    intro r hr
    have hr2 : 2 ≤ r := (Finset.mem_Icc.mp hr).1
    have hrle : r ≤ q - 1 := (Finset.mem_Icc.mp hr).2
    have hrlt : r < q := by omega
    have hrN : r ≤ N := by omega
    rw [ih r hrlt hr2 hrN]
  have hsum := heq q hq hqN
  rw [sum_Icc_two_split_top hq, sum_Icc_two_split_top hq] at hsum
  have hdiagq : beta q q != 0 := hdiag q hq hqN
  have hdiagq' : beta q q ≠ 0 := by
    simpa using hdiagq
  have hdiagTerm : beta q q * M q = beta q q * M' q := by
    linarith
  have hscaled := congrArg (fun x => (beta q q)⁻¹ * x) hdiagTerm
  have hEqOr : M q = M' q ∨ beta q q = 0 := by
    simpa [mul_assoc] using hscaled
  exact hEqOr.resolve_right hdiagq'

/-- Paper label: `thm:fold-infonce-loss-spectrum-identifiability`. -/
theorem paper_fold_infonce_loss_spectrum_identifiability (N : Nat) (beta : Nat → Nat → Real)
    (M M' : Nat → Real)
    (hdiag : ∀ K, 2 ≤ K → K ≤ N → beta K K != 0)
    (heq : ∀ K, 2 ≤ K → K ≤ N ->
      Finset.sum (Finset.Icc 2 K) (fun q => beta K q * M q) =
        Finset.sum (Finset.Icc 2 K) (fun q => beta K q * M' q)) :
    ∀ q, 2 ≤ q → q ≤ N → M q = M' q := by
  exact loss_spectrum_identifiability_aux N beta M M' hdiag heq

end Omega.Folding
