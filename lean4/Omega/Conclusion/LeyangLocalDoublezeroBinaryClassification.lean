import Mathlib.Tactic
import Omega.Zeta.XiLeyangSquareRootCollisionLeadingZerosN2
import Omega.Zeta.XiLeyangTwoLeadingZerosExtrapolateUc

namespace Omega.Conclusion

/-- The two normalized local kernels appearing in the Lee--Yang double-zero packet. -/
inductive conclusion_leyang_local_doublezero_binary_classification_kernel
  | sinh
  | cosh
  deriving DecidableEq

/-- The first squared zero location in the normalized `w`-coordinate. -/
def conclusion_leyang_local_doublezero_binary_classification_first_weight :
    conclusion_leyang_local_doublezero_binary_classification_kernel → ℚ
  | .sinh => 1
  | .cosh => Omega.Zeta.xiLeyangTwoLeadingNode 0 / 4

/-- The second squared zero location in the normalized `w`-coordinate. -/
def conclusion_leyang_local_doublezero_binary_classification_second_weight :
    conclusion_leyang_local_doublezero_binary_classification_kernel → ℚ
  | .sinh => 4
  | .cosh => Omega.Zeta.xiLeyangTwoLeadingNode 1 / 4

/-- The quadratic rescaling `u = u_* - η / (b_* m^2)` attached to the normalized zero weights. -/
def conclusion_leyang_local_doublezero_binary_classification_rescaled_zero
    (uStar bStar m weight : ℚ) : ℚ :=
  uStar - weight / (bStar * m ^ 2)

/-- The ratio of the first two limiting squared zero locations. -/
def conclusion_leyang_local_doublezero_binary_classification_distance_ratio
    (K : conclusion_leyang_local_doublezero_binary_classification_kernel) : ℚ :=
  conclusion_leyang_local_doublezero_binary_classification_second_weight K /
    conclusion_leyang_local_doublezero_binary_classification_first_weight K

/-- Paper label: `thm:conclusion-leyang-local-doublezero-binary-classification`.
The local double-zero packet has exactly two normalized kernels. Their first two squared zero
locations are `1, 4` in the `sinh` case and `1/4, 9/4` in the `cosh` case, so the quadratic
rescaling `u = u_* + w^2 / (b_* m^2)` yields the limiting nearest-zero ratios `4` and `9`. -/
theorem paper_conclusion_leyang_local_doublezero_binary_classification
    (uStar bStar m : ℚ) (hbStar : bStar ≠ 0) (hm : m ≠ 0) :
    Omega.Zeta.xiLeyangTwoLeadingNode 0 = 1 ∧
      Omega.Zeta.xiLeyangTwoLeadingNode 1 = 9 ∧
      conclusion_leyang_local_doublezero_binary_classification_distance_ratio .sinh = 4 ∧
      conclusion_leyang_local_doublezero_binary_classification_distance_ratio .cosh = 9 ∧
      ((conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_second_weight .sinh)) -
          uStar) /
          ((conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
              (conclusion_leyang_local_doublezero_binary_classification_first_weight .sinh)) -
            uStar) =
        4 ∧
      ((conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_second_weight .cosh)) -
          uStar) /
          ((conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
              (conclusion_leyang_local_doublezero_binary_classification_first_weight .cosh)) -
            uStar) =
        9 ∧
      ∀ K : conclusion_leyang_local_doublezero_binary_classification_kernel,
        K = .sinh ∨ K = .cosh := by
  have hbm2 : bStar * m ^ 2 ≠ 0 := mul_ne_zero hbStar (pow_ne_zero 2 hm)
  refine ⟨by norm_num [Omega.Zeta.xiLeyangTwoLeadingNode], by norm_num [Omega.Zeta.xiLeyangTwoLeadingNode],
    ?_, ?_, ?_, ?_, ?_⟩
  · norm_num [conclusion_leyang_local_doublezero_binary_classification_distance_ratio,
      conclusion_leyang_local_doublezero_binary_classification_first_weight,
      conclusion_leyang_local_doublezero_binary_classification_second_weight,
      Omega.Zeta.xiLeyangTwoLeadingNode]
  · norm_num [conclusion_leyang_local_doublezero_binary_classification_distance_ratio,
      conclusion_leyang_local_doublezero_binary_classification_first_weight,
      conclusion_leyang_local_doublezero_binary_classification_second_weight,
      Omega.Zeta.xiLeyangTwoLeadingNode]
  · have hfirst :
        conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_first_weight .sinh) -
          uStar =
          -(1 / (bStar * m ^ 2)) := by
      norm_num [conclusion_leyang_local_doublezero_binary_classification_rescaled_zero,
        conclusion_leyang_local_doublezero_binary_classification_first_weight]
    have hsecond :
        conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_second_weight .sinh) -
          uStar =
          -(4 / (bStar * m ^ 2)) := by
      norm_num [conclusion_leyang_local_doublezero_binary_classification_rescaled_zero,
        conclusion_leyang_local_doublezero_binary_classification_second_weight]
    rw [hfirst, hsecond]
    field_simp [hbm2]
  · have hfirst :
        conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_first_weight .cosh) -
          uStar =
          -((1 / 4 : ℚ) / (bStar * m ^ 2)) := by
      norm_num [conclusion_leyang_local_doublezero_binary_classification_rescaled_zero,
        conclusion_leyang_local_doublezero_binary_classification_first_weight,
        Omega.Zeta.xiLeyangTwoLeadingNode]
    have hsecond :
        conclusion_leyang_local_doublezero_binary_classification_rescaled_zero uStar bStar m
            (conclusion_leyang_local_doublezero_binary_classification_second_weight .cosh) -
          uStar =
          -((9 / 4 : ℚ) / (bStar * m ^ 2)) := by
      norm_num [conclusion_leyang_local_doublezero_binary_classification_rescaled_zero,
        conclusion_leyang_local_doublezero_binary_classification_second_weight,
        Omega.Zeta.xiLeyangTwoLeadingNode]
    rw [hfirst, hsecond]
    field_simp [hbm2]
  · intro K
    cases K <;> simp

end Omega.Conclusion
