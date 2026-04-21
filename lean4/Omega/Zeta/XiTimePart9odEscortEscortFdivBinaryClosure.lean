import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic
import Omega.Zeta.XiTimePart9odEscortTvCollapseBlockUniform
import Omega.Zeta.XiTimePart9odEscortTvCollapseExactBlockWeights

namespace Omega.Zeta

open scoped BigOperators goldenRatio

/-- Limiting escort parameter on the binary last-bit model. -/
noncomputable def xiEscortTheta (s : ℕ) : ℝ :=
  1 / (1 + Real.goldenRatio ^ (s + 1 : ℕ))

/-- Limiting Bernoulli law attached to the escort temperature `s`. -/
noncomputable def xiEscortBinaryLaw (s : ℕ) : Bool → ℝ
  | false => 1 - xiEscortTheta s
  | true => xiEscortTheta s

/-- Binary `f`-divergence between the two escort limit laws. -/
noncomputable def xiEscortBinaryFDivLimit (f : ℝ → ℝ) (p q : ℕ) : ℝ :=
  ∑ b : Bool, xiEscortBinaryLaw p b * f (xiEscortBinaryLaw q b / xiEscortBinaryLaw p b)

lemma xiEscortTheta_pos (s : ℕ) : 0 < xiEscortTheta s := by
  unfold xiEscortTheta
  positivity

lemma xiEscortTheta_lt_one (s : ℕ) : xiEscortTheta s < 1 := by
  unfold xiEscortTheta
  have hden : (1 : ℝ) < 1 + Real.goldenRatio ^ (s + 1 : ℕ) := by
    have hpow : 0 < Real.goldenRatio ^ (s + 1 : ℕ) := by positivity
    linarith
  simpa using (one_div_lt_one_div_of_lt (by norm_num : (0 : ℝ) < 1) hden)

lemma xiEscortTheta_one_sub_pos (s : ℕ) : 0 < 1 - xiEscortTheta s := by
  exact sub_pos.mpr (xiEscortTheta_lt_one s)

private lemma xiEscort_power_contribution (α a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    b * (a / b) ^ α = a ^ α * b ^ (1 - α) := by
  rw [Real.div_rpow ha hb.le, Real.rpow_sub hb, Real.rpow_one]
  ring

/-- Paper label: `thm:xi-time-part9od-escort-escort-fdiv-binary-closure`. -/
theorem paper_xi_time_part9od_escort_escort_fdiv_binary_closure (f : ℝ → ℝ) (p q : ℕ) :
    xiEscortBinaryFDivLimit f p q =
      (1 - xiEscortTheta p) * f ((1 - xiEscortTheta q) / (1 - xiEscortTheta p)) +
        xiEscortTheta p * f (xiEscortTheta q / xiEscortTheta p) := by
  simpa [xiEscortBinaryFDivLimit, xiEscortBinaryLaw, add_comm, add_left_comm, add_assoc]

/-- Closed power-sum form underlying the binary Rényi divergence. -/
theorem xiEscortBinaryFDivLimit_power (α : ℝ) (p q : ℕ) :
    xiEscortBinaryFDivLimit (fun u => u ^ α) p q =
      (1 - xiEscortTheta q) ^ α * (1 - xiEscortTheta p) ^ (1 - α) +
        xiEscortTheta q ^ α * xiEscortTheta p ^ (1 - α) := by
  rw [paper_xi_time_part9od_escort_escort_fdiv_binary_closure]
  rw [xiEscort_power_contribution α (1 - xiEscortTheta q) (1 - xiEscortTheta p)
      (sub_nonneg.mpr (le_of_lt (xiEscortTheta_lt_one q))) (xiEscortTheta_one_sub_pos p)]
  rw [xiEscort_power_contribution α (xiEscortTheta q) (xiEscortTheta p)
      (le_of_lt (xiEscortTheta_pos q)) (xiEscortTheta_pos p)]

/-- Rényi closed form extracted from the binary escort `f`-divergence. -/
theorem xiEscortBinaryRenyiClosedForm (α : ℝ) (p q : ℕ) :
    Real.log (xiEscortBinaryFDivLimit (fun u => u ^ α) p q) / (α - 1) =
      Real.log ((1 - xiEscortTheta q) ^ α * (1 - xiEscortTheta p) ^ (1 - α) +
        xiEscortTheta q ^ α * xiEscortTheta p ^ (1 - α)) / (α - 1) := by
  rw [xiEscortBinaryFDivLimit_power]

/-- KL specialization of the binary escort `f`-divergence. -/
noncomputable def xiEscortBinaryKLLimit (p q : ℕ) : ℝ :=
  (1 - xiEscortTheta q) * Real.log ((1 - xiEscortTheta q) / (1 - xiEscortTheta p)) +
    xiEscortTheta q * Real.log (xiEscortTheta q / xiEscortTheta p)

/-- The generator `f(u) = u log u` reduces the binary `f`-divergence to the Bernoulli KL form. -/
theorem xiEscortBinaryFDivLimit_kl (p q : ℕ) :
    xiEscortBinaryFDivLimit (fun u => u * Real.log u) p q = xiEscortBinaryKLLimit p q := by
  rw [paper_xi_time_part9od_escort_escort_fdiv_binary_closure]
  unfold xiEscortBinaryKLLimit
  set θp := xiEscortTheta p
  set θq := xiEscortTheta q
  have hθp : 0 < θp := by
    simpa [θp] using xiEscortTheta_pos p
  have h1θp : 0 < 1 - θp := by
    simpa [θp] using xiEscortTheta_one_sub_pos p
  calc
    (1 - θp) * (((1 - θq) / (1 - θp)) * Real.log ((1 - θq) / (1 - θp))) +
        θp * ((θq / θp) * Real.log (θq / θp)) =
      ((1 - θp) * ((1 - θq) / (1 - θp))) * Real.log ((1 - θq) / (1 - θp)) +
        (θp * (θq / θp)) * Real.log (θq / θp) := by
          ring
    _ = (1 - θq) * Real.log ((1 - θq) / (1 - θp)) + θq * Real.log (θq / θp) := by
          congr 1 <;> field_simp [hθp.ne', h1θp.ne']

end Omega.Zeta
