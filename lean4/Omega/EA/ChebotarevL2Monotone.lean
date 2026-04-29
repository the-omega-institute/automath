import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.EA

open scoped BigOperators

noncomputable section

/-- The finite fiber over a coarse Chebotarev label. -/
def chebotarevL2Fiber
    {α β : Type*} [Fintype α] [DecidableEq α] [DecidableEq β]
    (π : α → β) (b : β) : Finset α :=
  Finset.univ.filter fun a => π a = b

/-- The coarse relative Haar density is the uniform average of the fine density on each fiber. -/
def chebotarevCoarseRelativeHaarDensity
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (r : α → ℝ) (b : β) : ℝ :=
  (∑ a ∈ chebotarevL2Fiber π b, r a) / k

/-- The squared `L²` mass of the fine relative density, grouped fiberwise. -/
def chebotarevFineL2Sq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (r : α → ℝ) : ℝ :=
  ∑ b, (∑ a ∈ chebotarevL2Fiber π b, (r a) ^ 2) / k

/-- The squared `L²` mass of the coarse relative density obtained by fiber averaging. -/
def chebotarevCoarseL2Sq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (r : α → ℝ) : ℝ :=
  ∑ b, (chebotarevCoarseRelativeHaarDensity π k r b) ^ 2

/-- The coarse `L²` norm attached to the quotient-relative Haar density. -/
def chebotarevCoarseL2Norm
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (r : α → ℝ) : ℝ :=
  Real.sqrt (chebotarevCoarseL2Sq π k r)

/-- The fine `L²` norm attached to the grouped fine relative density. -/
def chebotarevFineL2Norm
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (r : α → ℝ) : ℝ :=
  Real.sqrt (chebotarevFineL2Sq π k r)

lemma chebotarev_coarse_sq_le_fine_sq
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (_hk : 0 < k) (hfiber : ∀ b : β, (chebotarevL2Fiber π b).card = k)
    (r : α → ℝ) :
    chebotarevCoarseL2Sq π k r ≤ chebotarevFineL2Sq π k r := by
  have hterm :
      ∀ b : β,
        (chebotarevCoarseRelativeHaarDensity π k r b) ^ 2 ≤
          (∑ a ∈ chebotarevL2Fiber π b, (r a) ^ 2) / k := by
    intro b
    unfold chebotarevCoarseRelativeHaarDensity
    simpa [hfiber b] using
      (sum_div_card_sq_le_sum_sq_div_card (s := chebotarevL2Fiber π b) (f := fun a => r a))
  unfold chebotarevCoarseL2Sq chebotarevFineL2Sq
  exact Finset.sum_le_sum (fun b _ => hterm b)

/-- Paper-facing `L²` monotonicity for quotient-relative Haar densities with equal-size fibers:
the coarse density is the fiber average of the fine density, and Jensen/orthogonal projection
contracts the `L²` norm.
    cor:kernel-chebotarev-L2-monotone -/
theorem paper_kernel_chebotarev_l2_monotone
    {α β : Type*} [Fintype α] [Fintype β] [DecidableEq α] [DecidableEq β]
    (π : α → β) (k : ℕ) (hk : 0 < k) (hfiber : ∀ b : β, (chebotarevL2Fiber π b).card = k)
    (r : α → ℝ) :
    chebotarevCoarseL2Norm π k r ≤ chebotarevFineL2Norm π k r := by
  unfold chebotarevCoarseL2Norm chebotarevFineL2Norm
  refine Real.sqrt_le_sqrt ?_
  exact chebotarev_coarse_sq_le_fine_sq π k hk hfiber r

end

end Omega.EA
