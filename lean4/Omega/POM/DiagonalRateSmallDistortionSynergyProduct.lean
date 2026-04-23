import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.SmallDistortionConstantTensorMultiplicative

namespace Omega.POM

private lemma pom_diagonal_rate_small_distortion_synergy_product_hellinger_pos {α : Type*}
    [Fintype α] (w : α → ℝ) (_hw : ∀ a, 0 ≤ w a)
    (hnontrivial : 0 < pomHellingerHalfSum w ^ 2 - 1) : 0 < pomHellingerHalfSum w := by
  have hnonneg : 0 ≤ pomHellingerHalfSum w := by
    classical
    unfold pomHellingerHalfSum
    exact Finset.sum_nonneg fun a _ => Real.sqrt_nonneg (w a)
  nlinarith

/-- Paper label: `thm:pom-diagonal-rate-small-distortion-synergy-product`. The tensor Hellinger
identity gives `1 + C_Ω = (1 + C_w) (1 + C_v)`, so the joint first-order coefficient is
`C_w + C_v + C_w C_v`. When both endpoint coefficients are positive, the extra product term makes
the joint coefficient strictly larger than the best separated first-order coefficient `C_w + C_v`,
and the corresponding log-gap is strictly positive. -/
theorem paper_pom_diagonal_rate_small_distortion_synergy_product {α β : Type*} [Fintype α]
    [Fintype β] (w : α → ℝ) (v : β → ℝ) (hw : ∀ a, 0 ≤ w a) (hv : ∀ b, 0 ≤ v b)
    (hw_nontrivial : 0 < pomHellingerHalfSum w ^ 2 - 1)
    (hv_nontrivial : 0 < pomHellingerHalfSum v ^ 2 - 1) :
    let Cw := pomHellingerHalfSum w ^ 2 - 1
    let Cv := pomHellingerHalfSum v ^ 2 - 1
    let Comega := pomHellingerHalfSum (pomTensorWeight w v) ^ 2 - 1
    Comega = Cw + Cv + Cw * Cv ∧
      Cw + Cv < Comega ∧
      0 < Real.log (1 + (Cw * Cv) / (Cw + Cv)) := by
  dsimp
  have hwpos :
      0 < pomHellingerHalfSum w :=
    pom_diagonal_rate_small_distortion_synergy_product_hellinger_pos w hw hw_nontrivial
  have hvpos :
      0 < pomHellingerHalfSum v :=
    pom_diagonal_rate_small_distortion_synergy_product_hellinger_pos v hv hv_nontrivial
  have hComega :
      pomHellingerHalfSum (pomTensorWeight w v) ^ 2 - 1 =
        (pomHellingerHalfSum w ^ 2 - 1) + (pomHellingerHalfSum v ^ 2 - 1) +
          (pomHellingerHalfSum w ^ 2 - 1) * (pomHellingerHalfSum v ^ 2 - 1) :=
    paper_pom_small_distortion_constant_tensor_multiplicative w v hw hv hwpos hvpos
  refine ⟨hComega, ?_, ?_⟩
  · have hprod_pos :
        0 < (pomHellingerHalfSum w ^ 2 - 1) * (pomHellingerHalfSum v ^ 2 - 1) := by
      exact mul_pos hw_nontrivial hv_nontrivial
    linarith
  · have hsum_pos :
        0 < (pomHellingerHalfSum w ^ 2 - 1) + (pomHellingerHalfSum v ^ 2 - 1) := by
      linarith
    have hfrac_pos :
        0 <
          ((pomHellingerHalfSum w ^ 2 - 1) * (pomHellingerHalfSum v ^ 2 - 1)) /
            ((pomHellingerHalfSum w ^ 2 - 1) + (pomHellingerHalfSum v ^ 2 - 1)) := by
      exact div_pos (mul_pos hw_nontrivial hv_nontrivial) hsum_pos
    have hone_lt :
        1 <
          1 +
            ((pomHellingerHalfSum w ^ 2 - 1) * (pomHellingerHalfSum v ^ 2 - 1)) /
              ((pomHellingerHalfSum w ^ 2 - 1) + (pomHellingerHalfSum v ^ 2 - 1)) := by
      linarith
    exact Real.log_pos hone_lt

end Omega.POM
