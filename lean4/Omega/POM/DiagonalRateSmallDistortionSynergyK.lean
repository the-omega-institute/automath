import Mathlib

namespace Omega.POM

open scoped BigOperators

structure DiagonalRateSmallDistortionSynergyKData where
  k : ℕ
  hk : 1 ≤ k
  coeff : Fin k → ℝ
  split : Fin k → ℝ
  hcoeff_nonneg : ∀ i, 0 ≤ coeff i
  hsplit_nonneg : ∀ i, 0 ≤ split i
  hsplit_sum : ∑ i, split i = 1

def DiagonalRateSmallDistortionSynergyKData.jointCoefficient
    (h : DiagonalRateSmallDistortionSynergyKData) : ℝ :=
  ∏ i, (1 + h.coeff i) - 1

def DiagonalRateSmallDistortionSynergyKData.separatedCoefficient
    (h : DiagonalRateSmallDistortionSynergyKData) : ℝ :=
  ∑ i, h.split i * h.coeff i

def DiagonalRateSmallDistortionSynergyKData.joint_expansion
    (h : DiagonalRateSmallDistortionSynergyKData) : Prop :=
  h.jointCoefficient = ∏ i, (1 + h.coeff i) - 1

def DiagonalRateSmallDistortionSynergyKData.separated_expansion
    (h : DiagonalRateSmallDistortionSynergyKData) : Prop :=
  h.separatedCoefficient ≤ ∑ i, h.coeff i

def DiagonalRateSmallDistortionSynergyKData.synergy_gap
    (h : DiagonalRateSmallDistortionSynergyKData) : Prop :=
  h.separatedCoefficient ≤ h.jointCoefficient

private lemma split_le_one (h : DiagonalRateSmallDistortionSynergyKData) (i : Fin h.k) :
    h.split i ≤ 1 := by
  have hrest_nonneg : 0 ≤ Finset.sum (Finset.univ.erase i) h.split := by
    exact Finset.sum_nonneg fun j _ => h.hsplit_nonneg j
  have hdecomp : h.split i + Finset.sum (Finset.univ.erase i) h.split = 1 := by
    simpa [Finset.sum_erase_add, Finset.mem_univ] using h.hsplit_sum
  linarith

private lemma oneAddSumLeProdOneAdd {α : Type*} [DecidableEq α] (s : Finset α) (f : α → ℝ)
    (hf : ∀ a ∈ s, 0 ≤ f a) : 1 + Finset.sum s f ≤ Finset.prod s (fun a => 1 + f a) := by
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hfa : 0 ≤ f a := hf a (by simp [ha])
      have hs_nonneg : 0 ≤ Finset.sum s f := by
        exact Finset.sum_nonneg fun b hb => hf b (by simp [hb])
      have hs_bound : 1 + Finset.sum s f ≤ Finset.prod s (fun b => 1 + f b) := by
        apply ih
        intro b hb
        exact hf b (by simp [hb])
      calc
        1 + Finset.sum (insert a s) f = 1 + f a + Finset.sum s f := by
          simp [ha, add_assoc, add_left_comm, add_comm]
        _ ≤ (1 + f a) * (1 + Finset.sum s f) := by
          nlinarith
        _ ≤ (1 + f a) * Finset.prod s (fun b => 1 + f b) := by
          gcongr
        _ = Finset.prod (insert a s) (fun b => 1 + f b) := by
          simp [ha]

/-- The multiplicativity of `1 + C_{1/2}` yields the joint endpoint coefficient, while any
separated allocation is bounded by the sum of coordinate coefficients. Since nonnegative tensor
cross-terms make `∏ᵢ (1 + Cᵢ) - 1` dominate `∑ᵢ Cᵢ`, the joint first-order coefficient strictly
improves on every separated split. -/
theorem paper_pom_diagonal_rate_small_distortion_synergy_k
    (h : DiagonalRateSmallDistortionSynergyKData) :
    h.joint_expansion ∧ h.separated_expansion ∧ h.synergy_gap := by
  refine ⟨rfl, ?_, ?_⟩
  · unfold DiagonalRateSmallDistortionSynergyKData.separated_expansion
    unfold DiagonalRateSmallDistortionSynergyKData.separatedCoefficient
    refine Finset.sum_le_sum ?_
    intro i _
    have hi0 : 0 ≤ h.split i := h.hsplit_nonneg i
    have hi1 : h.split i ≤ 1 := split_le_one h i
    have hci : 0 ≤ h.coeff i := h.hcoeff_nonneg i
    nlinarith
  · unfold DiagonalRateSmallDistortionSynergyKData.synergy_gap
    have hsep :
        h.separatedCoefficient ≤ ∑ i, h.coeff i := by
      unfold DiagonalRateSmallDistortionSynergyKData.separatedCoefficient
      refine Finset.sum_le_sum ?_
      intro i _
      have hi0 : 0 ≤ h.split i := h.hsplit_nonneg i
      have hi1 : h.split i ≤ 1 := split_le_one h i
      have hci : 0 ≤ h.coeff i := h.hcoeff_nonneg i
      nlinarith
    have hprod :
        1 + ∑ i, h.coeff i ≤ ∏ i, (1 + h.coeff i) := by
      exact oneAddSumLeProdOneAdd Finset.univ h.coeff fun i _ => h.hcoeff_nonneg i
    have hsum_to_joint : ∑ i, h.coeff i ≤ h.jointCoefficient := by
      unfold DiagonalRateSmallDistortionSynergyKData.jointCoefficient
      linarith
    exact le_trans hsep hsum_to_joint

end Omega.POM
