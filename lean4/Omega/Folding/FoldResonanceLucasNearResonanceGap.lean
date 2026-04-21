import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Folding.ShiftDynamics

namespace Omega.Folding

open scoped goldenRatio

/-- Re-export of the Lucas sequence into the `Omega.Folding` namespace for the folding-resonance
statements. -/
abbrev lucasNum : Nat → Nat := Omega.lucasNum

/-- Concrete zero families used by the Lucas near-resonance gap estimate: either a pure golden-ratio
point `φ^(n+2) / 2` or the Lucas-twisted point `L_n φ² / 2`. -/
def foldResonanceZero (z : Real) : Prop :=
  ∃ n : Nat,
    z = (1 / 2 : Real) * Real.goldenRatio ^ (n + 2) ∨
      z = ((lucasNum n : Real) / 2) * Real.goldenRatio ^ 2

private theorem goldenRatio_pow_add_two (n : Nat) :
    Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by
  calc
    Real.goldenRatio ^ (n + 2) = Real.goldenRatio ^ n * Real.goldenRatio ^ 2 := by
      rw [pow_add]
    _ = Real.goldenRatio ^ n * (Real.goldenRatio + 1) := by rw [Real.goldenRatio_sq]
    _ = Real.goldenRatio ^ (n + 1) + Real.goldenRatio ^ n := by ring

private theorem goldenConj_pow_add_two (n : Nat) :
    Real.goldenConj ^ (n + 2) = Real.goldenConj ^ (n + 1) + Real.goldenConj ^ n := by
  calc
    Real.goldenConj ^ (n + 2) = Real.goldenConj ^ n * Real.goldenConj ^ 2 := by
      rw [pow_add]
    _ = Real.goldenConj ^ n * (Real.goldenConj + 1) := by rw [Real.goldenConj_sq]
    _ = Real.goldenConj ^ (n + 1) + Real.goldenConj ^ n := by ring

private theorem lucas_binet : ∀ n : Nat,
    (lucasNum n : Real) = Real.goldenRatio ^ n + Real.goldenConj ^ n
  | 0 => by norm_num [lucasNum]
  | 1 => by simp [lucasNum, Real.goldenRatio_add_goldenConj]
  | n + 2 => by
      change ((Omega.lucasNum (n + 2) : Nat) : Real) =
        Real.goldenRatio ^ (n + 2) + Real.goldenConj ^ (n + 2)
      rw [Omega.lucasNum_succ_succ, Nat.cast_add, lucas_binet (n + 1), lucas_binet n,
        goldenRatio_pow_add_two n, goldenConj_pow_add_two n]
      ring

private lemma goldenConj_pow_even (m : Nat) :
    Real.goldenConj ^ (2 * m) = (Real.goldenRatio ^ (2 * m))⁻¹ := by
  have hconj : (Real.goldenConj : Real) = -(Real.goldenRatio⁻¹ : Real) := by
    have hinv : (Real.goldenRatio : Real)⁻¹ = -Real.goldenConj := by
      simpa [one_div] using Real.inv_goldenRatio
    linarith
  rw [hconj, show (-((Real.goldenRatio : Real)⁻¹)) ^ (2 * m) = ((Real.goldenRatio : Real)⁻¹) ^ (2 * m) by
    simp]
  rw [inv_pow]

/-- Paper label: `thm:fold-resonance-lucas-near-resonance-gap`.
The two explicit Lucas/golden-ratio zero families produce a gap of exact size `φ⁴ / (4x)`. -/
theorem paper_fold_resonance_lucas_near_resonance_gap (m : Nat) (hm : 2 <= m)
    (hm3 : m % 3 != 0) :
    let x : Real := (1 / 2 : Real) * Real.goldenRatio ^ (2 * m + 2)
    let y : Real := ((Omega.Folding.lucasNum (2 * m) : Real) / 2) * Real.goldenRatio ^ 2
    foldResonanceZero x ∧ foldResonanceZero y ∧ |x - y| = Real.goldenRatio ^ 4 / (4 * x) := by
  dsimp
  have hx_zero : foldResonanceZero ((1 / 2 : Real) * Real.goldenRatio ^ (2 * m + 2)) := by
    refine ⟨2 * m, Or.inl ?_⟩
    rfl
  have hy_zero :
      foldResonanceZero (((Omega.Folding.lucasNum (2 * m) : Real) / 2) * Real.goldenRatio ^ 2) := by
    refine ⟨2 * m, Or.inr ?_⟩
    rfl
  have hlucas :
      (Omega.Folding.lucasNum (2 * m) : Real) =
        Real.goldenRatio ^ (2 * m) + (Real.goldenRatio ^ (2 * m))⁻¹ := by
    rw [lucas_binet, goldenConj_pow_even]
  have hdiff :
      (((Omega.Folding.lucasNum (2 * m) : Real) / 2) * Real.goldenRatio ^ 2) -
          ((1 / 2 : Real) * Real.goldenRatio ^ (2 * m + 2)) =
        (1 / 2 : Real) * (Real.goldenRatio ^ (2 * m))⁻¹ * Real.goldenRatio ^ 2 := by
    rw [hlucas, pow_add, Real.goldenRatio_sq]
    ring
  have habs :
      |((1 / 2 : Real) * Real.goldenRatio ^ (2 * m + 2)) -
          (((Omega.Folding.lucasNum (2 * m) : Real) / 2) * Real.goldenRatio ^ 2)| =
        (1 / 2 : Real) * (Real.goldenRatio ^ (2 * m))⁻¹ * Real.goldenRatio ^ 2 := by
    rw [abs_sub_comm, abs_of_nonneg]
    · exact hdiff
    · rw [hdiff]
      positivity
  have htarget :
      (1 / 2 : Real) * (Real.goldenRatio ^ (2 * m))⁻¹ * Real.goldenRatio ^ 2 =
        Real.goldenRatio ^ 4 / (4 * ((1 / 2 : Real) * Real.goldenRatio ^ (2 * m + 2))) := by
    have hphi_ne : (Real.goldenRatio : Real) ≠ 0 := Real.goldenRatio_ne_zero
    have hpow_ne : (Real.goldenRatio ^ (2 * m) : Real) ≠ 0 := pow_ne_zero _ hphi_ne
    have hpow2_ne : (Real.goldenRatio ^ (2 * m + 2) : Real) ≠ 0 := pow_ne_zero _ hphi_ne
    rw [pow_add, div_eq_mul_inv]
    field_simp [hpow_ne, hpow2_ne]
    ring
  have _ : 2 ≤ m := hm
  have _ : (m % 3 != 0) = true := hm3
  refine ⟨hx_zero, hy_zero, ?_⟩
  rw [habs, htarget]

end Omega.Folding
