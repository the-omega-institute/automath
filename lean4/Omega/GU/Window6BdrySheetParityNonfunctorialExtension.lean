import Mathlib.Tactic
import Omega.GU.FreeInvolutionCount

namespace Omega.GU

/-- The number of fixed-point-free involutions on a fiber of size `d`.
Odd fibers contribute `0`, even fibers contribute the usual matching count. -/
def sheetFiberExtensionCount (d : ℕ) : ℕ :=
  if Even d then freeInvolutionCount (d / 2) else 0

/-- The total boundary sheet-extension count is the product of the independent fiber counts. -/
def sheetExtensionCount {W : Type*} [Fintype W] (fiberCard : W → ℕ) : ℕ :=
  ∏ w, sheetFiberExtensionCount (fiberCard w)

lemma sheetFiberExtensionCount_eq_doubleFactorial {d : ℕ} (hd : Even d) :
    sheetFiberExtensionCount d = Nat.doubleFactorial (d - 1) := by
  obtain ⟨r, rfl⟩ := hd
  rw [sheetFiberExtensionCount, if_pos (by simp)]
  have hdiv : (r + r) / 2 = r := by omega
  rw [hdiv]
  simpa [two_mul] using freeInvolutionCount_eq_doubleFactorial r

lemma sheetFiberExtensionCount_pos_iff_even (d : ℕ) :
    0 < sheetFiberExtensionCount d ↔ Even d := by
  constructor
  · intro h
    by_contra hd
    simp [sheetFiberExtensionCount, hd] at h
  · intro hd
    rw [sheetFiberExtensionCount_eq_doubleFactorial hd]
    exact Nat.doubleFactorial_pos _

/-- Paper-facing fixed-point-free boundary-sheet parity count:
existence is equivalent to even fiber cardinality, and on even fibers the count is the
fiberwise odd double-factorial product.
thm:window6-bdry-sheet-parity-nonfunctorial-extension -/
theorem paper_window6_bdry_sheet_parity_nonfunctorial_extension
    {W : Type*} [Fintype W] (fiberCard : W → ℕ) :
    (0 < sheetExtensionCount fiberCard ↔ ∀ w, Even (fiberCard w)) ∧
    ((∀ w, Even (fiberCard w)) →
      sheetExtensionCount fiberCard = ∏ w, Nat.doubleFactorial (fiberCard w - 1)) := by
  constructor
  · constructor
    · intro hprod w
      have hne : sheetFiberExtensionCount (fiberCard w) ≠ 0 := by
        have hprodne : sheetExtensionCount fiberCard ≠ 0 := Nat.ne_of_gt hprod
        intro hw0
        apply hprodne
        unfold sheetExtensionCount
        rw [Finset.prod_eq_zero_iff]
        exact ⟨w, Finset.mem_univ _, hw0⟩
      exact (sheetFiberExtensionCount_pos_iff_even _).1 (Nat.pos_iff_ne_zero.mpr hne)
    · intro hEven
      unfold sheetExtensionCount
      exact Finset.prod_pos fun w _ => (sheetFiberExtensionCount_pos_iff_even _).2 (hEven w)
  · intro hEven
    unfold sheetExtensionCount
    refine Finset.prod_congr rfl ?_
    intro w _
    exact sheetFiberExtensionCount_eq_doubleFactorial (hEven w)

end Omega.GU
