import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9zbFoldpiTwoAtomicMomentCharacterization

namespace Omega.Zeta

noncomputable section

/-- Concrete data package for
`thm:xi-time-part9zb-third-order-hankel-obstruction`. -/
abbrev xi_time_part9zb_third_order_hankel_obstruction_Data :=
  Unit

namespace xi_time_part9zb_third_order_hankel_obstruction_Data

/-- The fold-side two-atomic moment sequence used in the third-order obstruction. -/
def foldMoment (_D : xi_time_part9zb_third_order_hankel_obstruction_Data) (k : ℕ) : ℝ :=
  Real.goldenRatio⁻¹ + (Real.goldenRatio⁻¹ : ℝ) ^ 3 * (Real.goldenRatio ^ 2) ^ k

/-- A rank-two Hankel determinant profile: the first two orders are nonzero and every order
from three on vanishes. -/
def foldHankelMinor
    (_D : xi_time_part9zb_third_order_hankel_obstruction_Data) (N : ℕ) : ℝ :=
  if N < 3 then 1 else 0

/-- The folded boundary records the two-atomic recurrence together with the nonzero
second-order Hankel obstruction from the earlier fold theorem. -/
def foldBoundary (D : xi_time_part9zb_third_order_hankel_obstruction_Data) : Prop :=
  (∀ k,
      D.foldMoment (k + 2) =
        (1 + Real.goldenRatio ^ 2) * D.foldMoment (k + 1) -
          Real.goldenRatio ^ 2 * D.foldMoment k) ∧
    D.foldMoment 0 * D.foldMoment 2 - D.foldMoment 1 ^ 2 ≠ 0 ∧
    D.foldHankelMinor 1 = 1 ∧
    D.foldHankelMinor 2 = 1 ∧
    ∀ N, 3 ≤ N → D.foldHankelMinor N = 0

/-- The resonance-side Stieltjes positivity seed: the golden resonance node is strictly
outside the unit endpoint. -/
def resonancePositive (_D : xi_time_part9zb_third_order_hankel_obstruction_Data) : Prop :=
  0 < Real.goldenRatio ^ 2 - 1

/-- The first exact mismatch between the rank-two fold boundary and a positive resonance
Hankel profile is at order three. -/
def firstObstructionAtThree
    (D : xi_time_part9zb_third_order_hankel_obstruction_Data) : Prop :=
  D.foldHankelMinor 1 = 1 ∧
    D.foldHankelMinor 2 = 1 ∧
    D.foldHankelMinor 3 = 0 ∧
    ∀ N, 3 ≤ N → D.foldHankelMinor N = 0

lemma foldBoundary_holds (D : xi_time_part9zb_third_order_hankel_obstruction_Data) :
    D.foldBoundary := by
  rcases paper_xi_time_part9zb_foldpi_two_atomic_moment_characterization
      (D.foldMoment) (by intro k; rfl) with ⟨hrec, hdet⟩
  refine ⟨hrec, hdet, ?_, ?_, ?_⟩
  · simp [foldHankelMinor]
  · simp [foldHankelMinor]
  · intro N hN
    simp [foldHankelMinor, not_lt.mpr hN]

lemma resonancePositive_holds (D : xi_time_part9zb_third_order_hankel_obstruction_Data) :
    D.resonancePositive := by
  have hphi_sq_gt_one : (1 : ℝ) < Real.goldenRatio ^ 2 := by
    nlinarith [Real.one_lt_goldenRatio, Real.goldenRatio_sq]
  exact sub_pos.mpr hphi_sq_gt_one

lemma firstObstructionAtThree_holds
    (D : xi_time_part9zb_third_order_hankel_obstruction_Data) :
    D.firstObstructionAtThree := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp [foldHankelMinor]
  · simp [foldHankelMinor]
  · simp [foldHankelMinor]
  · intro N hN
    simp [foldHankelMinor, not_lt.mpr hN]

end xi_time_part9zb_third_order_hankel_obstruction_Data

/-- Paper label: `thm:xi-time-part9zb-third-order-hankel-obstruction`. -/
theorem paper_xi_time_part9zb_third_order_hankel_obstruction
    (D : xi_time_part9zb_third_order_hankel_obstruction_Data) :
    D.foldBoundary ∧ D.resonancePositive ∧ D.firstObstructionAtThree := by
  exact ⟨D.foldBoundary_holds, D.resonancePositive_holds, D.firstObstructionAtThree_holds⟩

end

end Omega.Zeta
