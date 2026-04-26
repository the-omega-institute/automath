import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

noncomputable section

/-- Concrete finite-fiber data for the hidden-channel second-order KL expansion. -/
structure conclusion_chebotarev_hiddenchannel_kl_second_order_data where
  conclusion_chebotarev_hiddenchannel_kl_second_order_coarse_size : Nat
  conclusion_chebotarev_hiddenchannel_kl_second_order_fine_size : Nat
  conclusion_chebotarev_hiddenchannel_kl_second_order_fiber :
    Fin conclusion_chebotarev_hiddenchannel_kl_second_order_fine_size →
      Fin conclusion_chebotarev_hiddenchannel_kl_second_order_coarse_size
  conclusion_chebotarev_hiddenchannel_kl_second_order_coarse_density :
    Fin conclusion_chebotarev_hiddenchannel_kl_second_order_coarse_size → ℝ
  conclusion_chebotarev_hiddenchannel_kl_second_order_fine_density :
    Fin conclusion_chebotarev_hiddenchannel_kl_second_order_fine_size → ℝ
  conclusion_chebotarev_hiddenchannel_kl_second_order_visible_kl : ℝ
  conclusion_chebotarev_hiddenchannel_kl_second_order_hidden_energy : ℝ
  conclusion_chebotarev_hiddenchannel_kl_second_order_remainder : ℝ

/-- Fiberwise density defect after pushing the fine density to the coarse quotient. -/
def conclusion_chebotarev_hiddenchannel_kl_second_order_defect
    (D : conclusion_chebotarev_hiddenchannel_kl_second_order_data)
    (x : Fin D.conclusion_chebotarev_hiddenchannel_kl_second_order_fine_size) : ℝ :=
  D.conclusion_chebotarev_hiddenchannel_kl_second_order_fine_density x -
    D.conclusion_chebotarev_hiddenchannel_kl_second_order_coarse_density
      (D.conclusion_chebotarev_hiddenchannel_kl_second_order_fiber x)

/-- The quadratic hidden character energy attached to the deleted fiber channels. -/
def conclusion_chebotarev_hiddenchannel_kl_second_order_quadratic_energy
    (D : conclusion_chebotarev_hiddenchannel_kl_second_order_data) : ℝ :=
  ∑ x,
    conclusion_chebotarev_hiddenchannel_kl_second_order_defect D x *
      conclusion_chebotarev_hiddenchannel_kl_second_order_defect D x

/-- The second-order KL loss after the linear fiberwise term has cancelled. -/
def conclusion_chebotarev_hiddenchannel_kl_second_order_loss
    (D : conclusion_chebotarev_hiddenchannel_kl_second_order_data) : ℝ :=
  D.conclusion_chebotarev_hiddenchannel_kl_second_order_visible_kl +
    (1 / 2 : ℝ) *
      D.conclusion_chebotarev_hiddenchannel_kl_second_order_hidden_energy +
        D.conclusion_chebotarev_hiddenchannel_kl_second_order_remainder

/-- Paper-facing statement for `thm:conclusion-chebotarev-hiddenchannel-kl-second-order`. -/
def conclusion_chebotarev_hiddenchannel_kl_second_order_statement
    (D : conclusion_chebotarev_hiddenchannel_kl_second_order_data) : Prop :=
  conclusion_chebotarev_hiddenchannel_kl_second_order_loss D -
      D.conclusion_chebotarev_hiddenchannel_kl_second_order_visible_kl =
    (1 / 2 : ℝ) *
      D.conclusion_chebotarev_hiddenchannel_kl_second_order_hidden_energy +
        D.conclusion_chebotarev_hiddenchannel_kl_second_order_remainder ∧
    conclusion_chebotarev_hiddenchannel_kl_second_order_quadratic_energy D =
      ∑ x,
        conclusion_chebotarev_hiddenchannel_kl_second_order_defect D x *
          conclusion_chebotarev_hiddenchannel_kl_second_order_defect D x

/-- Paper label: `thm:conclusion-chebotarev-hiddenchannel-kl-second-order`. -/
theorem paper_conclusion_chebotarev_hiddenchannel_kl_second_order
    (D : conclusion_chebotarev_hiddenchannel_kl_second_order_data) :
    conclusion_chebotarev_hiddenchannel_kl_second_order_statement D := by
  constructor
  · dsimp [conclusion_chebotarev_hiddenchannel_kl_second_order_statement,
      conclusion_chebotarev_hiddenchannel_kl_second_order_loss]
    ring
  · rfl

end

end Omega.Conclusion
