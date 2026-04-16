import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic
import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

open Finset
open scoped BigOperators

/-- Mixed monomials on the visible `B₃/C₃` weight support. -/
def mixedMonomial (a b c : Nat) (w : Weight) : ℤ :=
  (w.1 ^ a) * (w.2.1 ^ b) * (w.2.2 ^ c)

/-- The coefficient appearing in the third mixed derivative of the exponential generating
    function is the cubic coordinate product times the exponential term. -/
noncomputable def triaxialExpTerm (t : ℝ × ℝ × ℝ) (w : Weight) : ℝ :=
  (((w.1 * w.2.1 * w.2.2 : ℤ) : ℝ) *
    Real.exp ((w.1 : ℝ) * t.1 + (w.2.1 : ℝ) * t.2.1 + (w.2.2 : ℝ) * t.2.2))

lemma mixedMonomial_eq_zero_of_coordProd_eq_zero
    {a b c : Nat} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    {w : Weight} (hprod : w.1 * w.2.1 * w.2.2 = 0) :
    mixedMonomial a b c w = 0 := by
  have ha0 : a ≠ 0 := Nat.ne_of_gt ha
  have hb0 : b ≠ 0 := Nat.ne_of_gt hb
  have hc0 : c ≠ 0 := Nat.ne_of_gt hc
  have hzero : w.1 = 0 ∨ w.2.1 = 0 ∨ w.2.2 = 0 := by
    rcases mul_eq_zero.mp hprod with h12 | h3
    · rcases mul_eq_zero.mp h12 with h1 | h2
      exact Or.inl h1
      exact Or.inr <| Or.inl h2
    · exact Or.inr <| Or.inr h3
  rcases hzero with h1 | h2 | h3
  · simp [mixedMonomial, h1, ha0]
  · simp [mixedMonomial, h2, hb0]
  · simp [mixedMonomial, h3, hc0]

lemma triaxialExpTerm_eq_zero_of_coordProd_eq_zero
    {t : ℝ × ℝ × ℝ} {w : Weight} (hprod : w.1 * w.2.1 * w.2.2 = 0) :
    triaxialExpTerm t w = 0 := by
  simp [triaxialExpTerm, hprod]

/-- Paper wrapper for the triaxial selection law on the `window-6` visible `B₃/C₃` support:
    every mixed monomial with three positive exponents vanishes on the support, and therefore
    the third mixed derivative coefficient in the exponential generating function vanishes
    termwise.
    prop:window6-b3c3-triaxial-selection-ideal-factorization -/
theorem paper_window6_b3c3_triaxial_selection_ideal_factorization :
    (∀ a b c : Nat, 1 ≤ a → 1 ≤ b → 1 ≤ c →
      (Finset.sum b3VisibleSupport (fun w => mixedMonomial a b c w) = 0) ∧
      (Finset.sum c3VisibleSupport (fun w => mixedMonomial a b c w) = 0)) ∧
    (∀ t : ℝ × ℝ × ℝ,
      (Finset.sum b3VisibleSupport (fun w => triaxialExpTerm t w) = 0) ∧
      (Finset.sum c3VisibleSupport (fun w => triaxialExpTerm t w) = 0)) := by
  have hsupport :
      ∀ w ∈ b3VisibleSupport ∪ c3VisibleSupport, w.1 * w.2.1 * w.2.2 = 0 :=
    paper_window6_b3c3_visible_support_three_levi_planes_proof.2.2.2
  refine ⟨?_, ?_⟩
  · intro a b c ha hb hc
    refine ⟨?_, ?_⟩
    · refine sum_eq_zero ?_
      intro w hw
      exact mixedMonomial_eq_zero_of_coordProd_eq_zero ha hb hc <|
        hsupport w (by simp [hw])
    · refine sum_eq_zero ?_
      intro w hw
      exact mixedMonomial_eq_zero_of_coordProd_eq_zero ha hb hc <|
        hsupport w (by simp [hw])
  · intro t
    refine ⟨?_, ?_⟩
    · refine sum_eq_zero ?_
      intro w hw
      exact triaxialExpTerm_eq_zero_of_coordProd_eq_zero <|
        hsupport w (by simp [hw])
    · refine sum_eq_zero ?_
      intro w hw
      exact triaxialExpTerm_eq_zero_of_coordProd_eq_zero <|
        hsupport w (by simp [hw])

end Omega.GU
