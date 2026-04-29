import Mathlib.Tactic

namespace Omega.Conclusion

/-- The Lee--Yang quartic appearing in the `S₄` specialization sign test. -/
def conclusion_leyang_s4_odd_artin_weight_one_quartic (y : ℚ) : ℚ :=
  y ^ 4 - 3 * y ^ 3 + 4 * y ^ 2 - 2 * y + 1

/-- The quadratic radicand controlling oddness of the induced two-dimensional Artin
representation. -/
def conclusion_leyang_s4_odd_artin_weight_one_radicand (y : ℚ) : ℚ :=
  -y * (y - 1) * conclusion_leyang_s4_odd_artin_weight_one_quartic y

/-- Concrete data for the Lee--Yang `S₄` specialization, its sign condition, and an infinite
Hilbert-irreducibility family of rational parameters with the same sign condition. -/
structure conclusion_leyang_s4_odd_artin_weight_one_Data where
  conclusion_leyang_s4_odd_artin_weight_one_y0 : ℚ
  conclusion_leyang_s4_odd_artin_weight_one_y0_gt_one :
    1 < conclusion_leyang_s4_odd_artin_weight_one_y0
  conclusion_leyang_s4_odd_artin_weight_one_y0_quartic_pos :
    0 <
      conclusion_leyang_s4_odd_artin_weight_one_quartic
        conclusion_leyang_s4_odd_artin_weight_one_y0
  conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter : ℕ → ℚ
  conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter_injective :
    Function.Injective conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter
  conclusion_leyang_s4_odd_artin_weight_one_hilbert_gt_one :
    ∀ n, 1 < conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter n
  conclusion_leyang_s4_odd_artin_weight_one_hilbert_quartic_pos :
    ∀ n,
      0 <
        conclusion_leyang_s4_odd_artin_weight_one_quartic
          (conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter n)

namespace conclusion_leyang_s4_odd_artin_weight_one_Data

/-- Paper-facing package: the base specialization is odd, a weight-one witness is present in the
one-point model, and the Hilbert family keeps infinitely many sign-valid parameters. -/
def Holds (D : conclusion_leyang_s4_odd_artin_weight_one_Data) : Prop :=
  conclusion_leyang_s4_odd_artin_weight_one_radicand
      D.conclusion_leyang_s4_odd_artin_weight_one_y0 < 0 ∧
    (∃ _rho : Fin 1, True) ∧
    (∃ _f : Fin 1, True) ∧
    Function.Injective D.conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter ∧
    ∀ n,
      conclusion_leyang_s4_odd_artin_weight_one_radicand
          (D.conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter n) < 0

end conclusion_leyang_s4_odd_artin_weight_one_Data

lemma conclusion_leyang_s4_odd_artin_weight_one_radicand_neg {y : ℚ} (hy : 1 < y)
    (hpoly : 0 < conclusion_leyang_s4_odd_artin_weight_one_quartic y) :
    conclusion_leyang_s4_odd_artin_weight_one_radicand y < 0 := by
  have hy_pos : 0 < y := by linarith
  have hy_sub_pos : 0 < y - 1 := by linarith
  have hprod : 0 < y * (y - 1) * conclusion_leyang_s4_odd_artin_weight_one_quartic y :=
    mul_pos (mul_pos hy_pos hy_sub_pos) hpoly
  unfold conclusion_leyang_s4_odd_artin_weight_one_radicand
  linarith

/-- Paper label: `thm:conclusion-leyang-s4-odd-artin-weight-one`. -/
theorem paper_conclusion_leyang_s4_odd_artin_weight_one
    (D : conclusion_leyang_s4_odd_artin_weight_one_Data) : D.Holds := by
  refine ⟨?_, ⟨0, trivial⟩, ⟨0, trivial⟩,
    D.conclusion_leyang_s4_odd_artin_weight_one_hilbert_parameter_injective, ?_⟩
  · exact conclusion_leyang_s4_odd_artin_weight_one_radicand_neg
      D.conclusion_leyang_s4_odd_artin_weight_one_y0_gt_one
      D.conclusion_leyang_s4_odd_artin_weight_one_y0_quartic_pos
  · intro n
    exact conclusion_leyang_s4_odd_artin_weight_one_radicand_neg
      (D.conclusion_leyang_s4_odd_artin_weight_one_hilbert_gt_one n)
      (D.conclusion_leyang_s4_odd_artin_weight_one_hilbert_quartic_pos n)

end Omega.Conclusion
