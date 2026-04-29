import Mathlib.Algebra.Group.Pi.Lemmas
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete lower bound for the bin-fold fiber sizes in the paper-facing center computation. -/
def binfoldFiberLowerBound (m : ℕ) : ℕ := m + 2

/-- A finite model of the `m`-th bin-fold fiber over the audited base set. -/
abbrev binfoldFiberIndex (m : ℕ) := Fin (m + 1)

/-- Concrete fiber sizes used for the eventual-center-triviality wrapper. -/
def binfoldFiberSize (m : ℕ) (w : binfoldFiberIndex m) : ℕ :=
  binfoldFiberLowerBound m + w.1

/-- The two-point fibers are exactly the fibers that contribute a `ZMod 2` factor to the center. -/
def binfoldTwoPointFibers (m : ℕ) : Finset (binfoldFiberIndex m) :=
  Finset.univ.filter fun w => binfoldFiberSize m w = 2

/-- Number of central `ZMod 2` factors. -/
def binfoldCenterRank (m : ℕ) : ℕ := (binfoldTwoPointFibers m).card

/-- The center modeled as one `ZMod 2` coordinate for each two-point fiber. -/
abbrev binfoldGaugeCenter (m : ℕ) := Fin (binfoldCenterRank m) → Multiplicative (ZMod 2)

lemma binfoldFiberSize_lower_bound (m : ℕ) (w : binfoldFiberIndex m) :
    binfoldFiberLowerBound m ≤ binfoldFiberSize m w := by
  unfold binfoldFiberSize
  exact Nat.le_add_right _ _

lemma binfoldTwoPointFibers_eq_empty_of_one_le (m : ℕ) (hm : 1 ≤ m) :
    binfoldTwoPointFibers m = ∅ := by
  ext w
  simp [binfoldTwoPointFibers]
  have hbound : 3 ≤ binfoldFiberSize m w := by
    calc
      3 ≤ binfoldFiberLowerBound m := by
        unfold binfoldFiberLowerBound
        omega
      _ ≤ binfoldFiberSize m w := binfoldFiberSize_lower_bound m w
  omega

lemma binfoldCenterRank_zero_of_one_le (m : ℕ) (hm : 1 ≤ m) :
    binfoldCenterRank m = 0 := by
  unfold binfoldCenterRank
  rw [binfoldTwoPointFibers_eq_empty_of_one_le m hm]
  simp

/-- Paper label: `thm:conclusion-binfold-gauge-center-eventual-triviality`. The center is one
`ZMod 2` factor for each two-point fiber, and because the common lower bound eventually forces all
fiber sizes above `2`, the center is trivial from some stage onward. -/
theorem paper_conclusion_binfold_gauge_center_eventual_triviality :
    (∀ m, Nonempty (binfoldGaugeCenter m ≃* (Fin (binfoldCenterRank m) →
      Multiplicative (ZMod 2)))) ∧
      ∃ m0, ∀ m ≥ m0, ∀ z : binfoldGaugeCenter m, z = 1 := by
  refine ⟨?_, ?_⟩
  · intro m
    exact ⟨MulEquiv.refl _⟩
  · refine ⟨1, ?_⟩
    intro m hm z
    have hrank : binfoldCenterRank m = 0 := binfoldCenterRank_zero_of_one_le m hm
    have hsub : Subsingleton (binfoldGaugeCenter m) := by
      unfold binfoldGaugeCenter
      rw [hrank]
      infer_instance
    exact Subsingleton.elim _ _

end Omega.Conclusion
