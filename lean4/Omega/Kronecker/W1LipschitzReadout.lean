import Mathlib.Tactic
import Omega.POM.CouplingExpectationBound

namespace Omega.Kronecker

open Omega.POM.CouplingExpectationBound

variable {α ι : Type*}

/-- Absolute gap between the two empirical readout expectations. -/
noncomputable def empiricalReadoutGap (Ω : Finset α) (f : ℝ → ℝ) (X Y : α → ℝ) : ℝ :=
  |expectation Ω (fun ω => f (X ω)) - expectation Ω (fun ω => f (Y ω))|

/-- The empirical `W₁` cost is the infimum of the transport costs over the available couplings. -/
noncomputable def empiricalW1 (Ω : Finset α) (π : ι → α → ℝ × ℝ) : ℝ :=
  sInf (Set.range fun i : ι => expectation Ω (fun ω => |(π i ω).1 - (π i ω).2|))

theorem coupling_readout_gap_le (Ω : Finset α) (hΩ : 0 < Ω.card) (f : ℝ → ℝ) (L : ℝ)
    (hLipschitz : ∀ x y, |f x - f y| ≤ L * |x - y|) (X Y : α → ℝ) (π : ι → α → ℝ × ℝ)
    (hleft : ∀ i, expectation Ω (fun ω => f (X ω)) = expectation Ω (fun ω => f ((π i ω).1)))
    (hright : ∀ i, expectation Ω (fun ω => f (Y ω)) = expectation Ω (fun ω => f ((π i ω).2)))
    (i : ι) :
    empiricalReadoutGap Ω f X Y ≤ L * expectation Ω (fun ω => |(π i ω).1 - (π i ω).2|) := by
  have hcard_pos : (0 : ℝ) < (Ω.card : ℝ) := by
    exact_mod_cast hΩ
  have hpoint :
      expectation Ω (fun ω => |f ((π i ω).1) - f ((π i ω).2)|) ≤
        expectation Ω (fun ω => L * |(π i ω).1 - (π i ω).2|) := by
    unfold expectation
    apply div_le_div_of_nonneg_right ?_ hcard_pos.le
    apply Finset.sum_le_sum
    intro ω hω
    exact hLipschitz _ _
  have hscale :
      expectation Ω (fun ω => L * |(π i ω).1 - (π i ω).2|) =
        L * expectation Ω (fun ω => |(π i ω).1 - (π i ω).2|) := by
    unfold expectation
    rw [← Finset.mul_sum, mul_div_assoc]
  calc
    empiricalReadoutGap Ω f X Y
        = |expectation Ω (fun ω => f ((π i ω).1)) -
            expectation Ω (fun ω => f ((π i ω).2))| := by
              unfold empiricalReadoutGap
              rw [hleft i, hright i]
    _ ≤ expectation Ω (fun ω => |f ((π i ω).1) - f ((π i ω).2)|) := by
          exact abs_expectation_sub_le Ω (fun ω => f ((π i ω).1)) (fun ω => f ((π i ω).2))
    _ ≤ expectation Ω (fun ω => L * |(π i ω).1 - (π i ω).2|) := hpoint
    _ = L * expectation Ω (fun ω => |(π i ω).1 - (π i ω).2|) := hscale

/-- Paper theorem: any Lipschitz readout gap is bounded by the infimum over coupling costs. -/
theorem paper_kronecker_w1_lipschitz_readout [Nonempty ι] (Ω : Finset α) (hΩ : 0 < Ω.card)
    (f : ℝ → ℝ) (L : ℝ) (hL : 0 < L) (X Y : α → ℝ) (π : ι → α → ℝ × ℝ)
    (hLipschitz : ∀ x y, |f x - f y| ≤ L * |x - y|)
    (hleft : ∀ i, expectation Ω (fun ω => f (X ω)) = expectation Ω (fun ω => f ((π i ω).1)))
    (hright : ∀ i, expectation Ω (fun ω => f (Y ω)) = expectation Ω (fun ω => f ((π i ω).2))) :
    empiricalReadoutGap Ω f X Y ≤ L * empiricalW1 Ω π := by
  classical
  let i0 : ι := Classical.choice ‹Nonempty ι›
  have hdiv : empiricalReadoutGap Ω f X Y / L ≤ empiricalW1 Ω π := by
    unfold empiricalW1
    refine le_csInf ?_ ?_
    · exact
        ⟨expectation Ω (fun ω => |(π i0 ω).1 - (π i0 ω).2|), Set.mem_range_self i0⟩
    · intro c hc
      rcases hc with ⟨i, rfl⟩
      exact
        (div_le_iff₀ hL).2 (by
          simpa [mul_comm] using
            (coupling_readout_gap_le Ω hΩ f L hLipschitz X Y π hleft hright i))
  simpa [mul_comm] using (div_le_iff₀ hL).1 hdiv

end Omega.Kronecker
