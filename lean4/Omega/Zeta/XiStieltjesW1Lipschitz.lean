import Mathlib.Tactic
import Omega.Kronecker.W1LipschitzReadout

namespace Omega.Zeta

open Omega.Kronecker
open Omega.POM.CouplingExpectationBound

/-- The Stieltjes readout kernel `a ↦ (t + a)⁻¹` on the depth axis. -/
noncomputable def xi_stieltjes_w1_lipschitz_kernel (t a : ℝ) : ℝ :=
  1 / (t + a)

/-- Finite-coupling package for the Stieltjes `W₁` readout audit. -/
structure xi_stieltjes_w1_lipschitz_data where
  α : Type
  couplingCount : ℕ
  Ω : Finset α
  hΩ : 0 < Ω.card
  t : ℝ
  ht : 0 < t
  depthLeft : α → ℝ
  depthRight : α → ℝ
  hdepthLeft : ∀ ω, 1 ≤ depthLeft ω
  hdepthRight : ∀ ω, 1 ≤ depthRight ω
  π : Fin (couplingCount + 1) → α → ℝ × ℝ
  hpiLeft : ∀ i ω, 1 ≤ (π i ω).1
  hpiRight : ∀ i ω, 1 ≤ (π i ω).2
  hleft :
    ∀ i,
      expectation Ω (fun ω => xi_stieltjes_w1_lipschitz_kernel t (depthLeft ω)) =
        expectation Ω (fun ω => xi_stieltjes_w1_lipschitz_kernel t ((π i ω).1))
  hright :
    ∀ i,
      expectation Ω (fun ω => xi_stieltjes_w1_lipschitz_kernel t (depthRight ω)) =
        expectation Ω (fun ω => xi_stieltjes_w1_lipschitz_kernel t ((π i ω).2))

namespace xi_stieltjes_w1_lipschitz_data

def bound (D : xi_stieltjes_w1_lipschitz_data) : Prop :=
  empiricalReadoutGap D.Ω (xi_stieltjes_w1_lipschitz_kernel D.t) D.depthLeft D.depthRight ≤
    (1 / (D.t + 1) ^ 2) * empiricalW1 D.Ω D.π

end xi_stieltjes_w1_lipschitz_data

open xi_stieltjes_w1_lipschitz_data

private lemma xi_stieltjes_w1_lipschitz_kernel_lipschitz (t a b : ℝ) (ht : 0 < t)
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    |xi_stieltjes_w1_lipschitz_kernel t a - xi_stieltjes_w1_lipschitz_kernel t b| ≤
      (1 / (t + 1) ^ 2) * |a - b| := by
  have hta : 0 < t + a := by
    linarith
  have htb : 0 < t + b := by
    linarith
  have hprod_pos : 0 < (t + a) * (t + b) := mul_pos hta htb
  have hsquare_pos : 0 < (t + 1) ^ 2 := by
    positivity
  have hkernel :
      xi_stieltjes_w1_lipschitz_kernel t a - xi_stieltjes_w1_lipschitz_kernel t b =
        (b - a) / ((t + a) * (t + b)) := by
    unfold xi_stieltjes_w1_lipschitz_kernel
    field_simp [hta.ne', htb.ne']
    ring
  have habs :
      |xi_stieltjes_w1_lipschitz_kernel t a - xi_stieltjes_w1_lipschitz_kernel t b| =
        |a - b| / ((t + a) * (t + b)) := by
    rw [hkernel, abs_div, abs_sub_comm, abs_of_pos hprod_pos]
  have hprod_ge : (t + 1) ^ 2 ≤ (t + a) * (t + b) := by
    nlinarith [ha, hb, ht.le]
  have hrecip :
      1 / ((t + a) * (t + b)) ≤ 1 / (t + 1) ^ 2 := by
    exact one_div_le_one_div_of_le hsquare_pos hprod_ge
  calc
    |xi_stieltjes_w1_lipschitz_kernel t a - xi_stieltjes_w1_lipschitz_kernel t b|
        = |a - b| * (1 / ((t + a) * (t + b))) := by
            rw [habs, div_eq_mul_one_div]
    _ ≤ |a - b| * (1 / (t + 1) ^ 2) := by
          exact mul_le_mul_of_nonneg_left hrecip (abs_nonneg _)
    _ = (1 / (t + 1) ^ 2) * |a - b| := by
          ring

private theorem xi_stieltjes_w1_lipschitz_coupling_gap_le (D : xi_stieltjes_w1_lipschitz_data)
    (i : Fin (D.couplingCount + 1)) :
    empiricalReadoutGap D.Ω (xi_stieltjes_w1_lipschitz_kernel D.t) D.depthLeft D.depthRight ≤
      (1 / (D.t + 1) ^ 2) * expectation D.Ω (fun ω => |(D.π i ω).1 - (D.π i ω).2|) := by
  have hcard_pos : (0 : ℝ) < (D.Ω.card : ℝ) := by
    exact_mod_cast D.hΩ
  have hpoint :
      expectation D.Ω
          (fun ω =>
            |xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).1) -
              xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).2)|) ≤
        expectation D.Ω (fun ω => (1 / (D.t + 1) ^ 2) * |(D.π i ω).1 - (D.π i ω).2|) := by
    unfold expectation
    apply div_le_div_of_nonneg_right ?_ hcard_pos.le
    apply Finset.sum_le_sum
    intro ω hω
    exact xi_stieltjes_w1_lipschitz_kernel_lipschitz D.t ((D.π i ω).1) ((D.π i ω).2) D.ht
      (D.hpiLeft i ω) (D.hpiRight i ω)
  have hscale :
      expectation D.Ω (fun ω => (1 / (D.t + 1) ^ 2) * |(D.π i ω).1 - (D.π i ω).2|) =
        (1 / (D.t + 1) ^ 2) * expectation D.Ω (fun ω => |(D.π i ω).1 - (D.π i ω).2|) := by
    unfold expectation
    rw [← Finset.mul_sum, mul_div_assoc]
  calc
    empiricalReadoutGap D.Ω (xi_stieltjes_w1_lipschitz_kernel D.t) D.depthLeft D.depthRight
        = |expectation D.Ω
              (fun ω => xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).1)) -
            expectation D.Ω
              (fun ω => xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).2))| := by
              unfold empiricalReadoutGap
              rw [D.hleft i, D.hright i]
    _ ≤ expectation D.Ω
          (fun ω =>
            |xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).1) -
              xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).2)|) := by
          exact
            abs_expectation_sub_le D.Ω
              (fun ω => xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).1))
              (fun ω => xi_stieltjes_w1_lipschitz_kernel D.t ((D.π i ω).2))
    _ ≤ expectation D.Ω (fun ω => (1 / (D.t + 1) ^ 2) * |(D.π i ω).1 - (D.π i ω).2|) := hpoint
    _ = (1 / (D.t + 1) ^ 2) * expectation D.Ω (fun ω => |(D.π i ω).1 - (D.π i ω).2|) := hscale

/-- Paper label: `prop:xi-stieltjes-w1-lipschitz`. -/
theorem paper_xi_stieltjes_w1_lipschitz (D : xi_stieltjes_w1_lipschitz_data) : D.bound := by
  classical
  have hL : 0 < 1 / (D.t + 1) ^ 2 := by
    have ht1 : 0 < D.t + 1 := by
      nlinarith [D.ht]
    exact one_div_pos.mpr (sq_pos_of_pos ht1)
  let i0 : Fin (D.couplingCount + 1) := ⟨0, Nat.succ_pos _⟩
  have hdiv :
      empiricalReadoutGap D.Ω (xi_stieltjes_w1_lipschitz_kernel D.t) D.depthLeft D.depthRight /
          (1 / (D.t + 1) ^ 2) ≤
        empiricalW1 D.Ω D.π := by
    unfold empiricalW1
    refine le_csInf ?_ ?_
    · exact
        ⟨expectation D.Ω (fun ω => |(D.π i0 ω).1 - (D.π i0 ω).2|), Set.mem_range_self i0⟩
    · intro c hc
      rcases hc with ⟨i, rfl⟩
      exact
        (div_le_iff₀ hL).2 (by
          simpa [mul_comm] using xi_stieltjes_w1_lipschitz_coupling_gap_le D i)
  unfold xi_stieltjes_w1_lipschitz_data.bound
  simpa [mul_comm] using (div_le_iff₀ hL).1 hdiv

end Omega.Zeta
