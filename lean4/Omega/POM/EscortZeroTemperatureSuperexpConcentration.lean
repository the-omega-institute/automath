import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Paper label: `cor:pom-escort-zero-temperature-superexp-concentration`. -/
theorem paper_pom_escort_zero_temperature_superexp_concentration {X : Type*} [Fintype X]
    (d : X → Real) (A : Finset X) (M epsilon : Real) (q m : Nat) (hq : 1 ≤ q)
    (hden : 0 < ∑ x : X, d x ^ q)
    (hA :
      ∀ x, x ∈ A → d x ^ q ≤ M ^ q * Real.exp (-(q : Real) * epsilon * (m : Real)))
    (hM : M ^ q ≤ ∑ x : X, d x ^ q) :
    (∑ x ∈ A, d x ^ q) / (∑ x : X, d x ^ q) ≤
      (Fintype.card X : Real) * Real.exp (-(q : Real) * epsilon * (m : Real)) := by
  have _ : 1 ≤ q := hq
  let Z : Real := ∑ x : X, d x ^ q
  let penalty : Real := Real.exp (-(q : Real) * epsilon * (m : Real))
  have hpenalty_nonneg : 0 ≤ penalty := le_of_lt (Real.exp_pos _)
  have hM_penalty : M ^ q * penalty ≤ Z * penalty := by
    exact mul_le_mul_of_nonneg_right hM hpenalty_nonneg
  have hsum_le_Acard :
      (∑ x ∈ A, d x ^ q) ≤ (A.card : Real) * (Z * penalty) := by
    calc
      (∑ x ∈ A, d x ^ q) ≤ ∑ x ∈ A, M ^ q * penalty := by
        exact Finset.sum_le_sum (fun x hx => hA x hx)
      _ = (A.card : Real) * (M ^ q * penalty) := by
        simp [penalty]
      _ ≤ (A.card : Real) * (Z * penalty) := by
        exact mul_le_mul_of_nonneg_left hM_penalty (by positivity)
  have hcard_le : (A.card : Real) ≤ (Fintype.card X : Real) := by
    exact_mod_cast A.card_le_univ
  have hZ_penalty_nonneg : 0 ≤ Z * penalty :=
    mul_nonneg (le_of_lt hden) hpenalty_nonneg
  have hsum_le :
      (∑ x ∈ A, d x ^ q) ≤ (Fintype.card X : Real) * (Z * penalty) := by
    exact hsum_le_Acard.trans (mul_le_mul_of_nonneg_right hcard_le hZ_penalty_nonneg)
  calc
    (∑ x ∈ A, d x ^ q) / (∑ x : X, d x ^ q)
        ≤ ((Fintype.card X : Real) * (Z * penalty)) / Z := by
          exact div_le_div_of_nonneg_right hsum_le (le_of_lt hden)
    _ = (Fintype.card X : Real) * penalty := by
      have hZ_ne : Z ≠ 0 := ne_of_gt hden
      field_simp [hZ_ne]

end Omega.POM
