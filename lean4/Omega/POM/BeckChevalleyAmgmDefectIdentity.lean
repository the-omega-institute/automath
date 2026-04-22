import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The concrete two-fiber space obtained from a two-point outer fiber with inner cardinalities
`a` and `b`. -/
abbrev TwoFiberSpace (a b : ℕ) := Sum (Fin a) (Fin b)

/-- The sequential uniform lift `L_f L_g` in the two-fiber model. -/
noncomputable def sequentialUniformLift (a b : ℕ) : TwoFiberSpace a b → ℝ
  | Sum.inl _ => 1 / (2 * (a : ℝ))
  | Sum.inr _ => 1 / (2 * (b : ℝ))

/-- The direct uniform lift `L_{g ∘ f}` in the two-fiber model. -/
noncomputable def directUniformLift (a b : ℕ) : TwoFiberSpace a b → ℝ
  | _ => 1 / ((a : ℝ) + b)

/-- Shannon entropy for a finite real-valued weight function. -/
noncomputable def shannonEntropy {α : Type*} [Fintype α] (p : α → ℝ) : ℝ :=
  -∑ x, p x * Real.log (p x)

/-- Kullback-Leibler divergence for a finite real-valued weight function. -/
noncomputable def klDiv {α : Type*} [Fintype α] (p q : α → ℝ) : ℝ :=
  ∑ x, p x * Real.log (p x / q x)

/-- The two-fiber AM-GM defect written in a form that is convenient for the equality criterion. -/
noncomputable def twoFiberAmgmDefect (a b : ℕ) : ℝ :=
  Real.log ((((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b)) / 2

lemma shannonEntropy_directUniformLift (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    shannonEntropy (directUniformLift a b) = Real.log ((a : ℝ) + b) := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsum :
      ∑ x : TwoFiberSpace a b, directUniformLift a b x * Real.log (directUniformLift a b x) =
        ((a : ℝ) + b) * (1 / ((a : ℝ) + b) * Real.log (1 / ((a : ℝ) + b))) := by
    rw [Fintype.sum_sum_type]
    simp [directUniformLift]
    ring
  calc
    shannonEntropy (directUniformLift a b)
        = -(((a : ℝ) + b) * (1 / ((a : ℝ) + b) * Real.log (1 / ((a : ℝ) + b)))) := by
            rw [shannonEntropy, hsum]
    _ = -((((a : ℝ) + b) * (1 / ((a : ℝ) + b))) * Real.log (1 / ((a : ℝ) + b))) := by ring
    _ = -(Real.log (1 / ((a : ℝ) + b))) := by
      have hMul : ((a : ℝ) + b) * (1 / ((a : ℝ) + b)) = 1 := by
        field_simp [haR.ne', hbR.ne']
      rw [hMul, one_mul]
    _ = Real.log ((a : ℝ) + b) := by
      rw [one_div, Real.log_inv, neg_neg]

lemma shannonEntropy_sequentialUniformLift (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    shannonEntropy (sequentialUniformLift a b) =
      (Real.log (2 * (a : ℝ)) + Real.log (2 * (b : ℝ))) / 2 := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsum :
      ∑ x : TwoFiberSpace a b, sequentialUniformLift a b x * Real.log (sequentialUniformLift a b x) =
        (a : ℝ) * (1 / (2 * (a : ℝ)) * Real.log (1 / (2 * (a : ℝ)))) +
          (b : ℝ) * (1 / (2 * (b : ℝ)) * Real.log (1 / (2 * (b : ℝ)))) := by
    rw [Fintype.sum_sum_type]
    simp [sequentialUniformLift]
  have hHalfA : (a : ℝ) * (1 / (2 * (a : ℝ))) = 1 / 2 := by
    field_simp [haR.ne']
  have hHalfB : (b : ℝ) * (1 / (2 * (b : ℝ))) = 1 / 2 := by
    field_simp [hbR.ne']
  calc
    shannonEntropy (sequentialUniformLift a b)
        = -((a : ℝ) * (1 / (2 * (a : ℝ)) * Real.log (1 / (2 * (a : ℝ)))) +
            (b : ℝ) * (1 / (2 * (b : ℝ)) * Real.log (1 / (2 * (b : ℝ))))) := by
            rw [shannonEntropy, hsum]
    _ = -(((a : ℝ) * (1 / (2 * (a : ℝ)))) * Real.log (1 / (2 * (a : ℝ))) +
          ((b : ℝ) * (1 / (2 * (b : ℝ)))) * Real.log (1 / (2 * (b : ℝ)))) := by
      ring
    _ = -((1 / 2 : ℝ) * Real.log (1 / (2 * (a : ℝ))) +
          (1 / 2 : ℝ) * Real.log (1 / (2 * (b : ℝ)))) := by
      rw [hHalfA, hHalfB]
    _ = (Real.log (2 * (a : ℝ)) + Real.log (2 * (b : ℝ))) / 2 := by
      rw [show 1 / (2 * (a : ℝ)) = (2 * (a : ℝ))⁻¹ by ring, Real.log_inv]
      rw [show 1 / (2 * (b : ℝ)) = (2 * (b : ℝ))⁻¹ by ring, Real.log_inv]
      ring

lemma klDiv_sequential_direct (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    klDiv (sequentialUniformLift a b) (directUniformLift a b) = twoFiberAmgmDefect a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  have hsum :
      klDiv (sequentialUniformLift a b) (directUniformLift a b) =
        (a : ℝ) * (1 / (2 * (a : ℝ)) *
          Real.log ((1 / (2 * (a : ℝ))) / (1 / ((a : ℝ) + b)))) +
          (b : ℝ) * (1 / (2 * (b : ℝ)) *
            Real.log ((1 / (2 * (b : ℝ))) / (1 / ((a : ℝ) + b)))) := by
    rw [klDiv, Fintype.sum_sum_type]
    simp [sequentialUniformLift, directUniformLift]
  have hHalfA : (a : ℝ) * (1 / (2 * (a : ℝ))) = 1 / 2 := by
    field_simp [haR.ne']
  have hHalfB : (b : ℝ) * (1 / (2 * (b : ℝ))) = 1 / 2 := by
    field_simp [hbR.ne']
  have hRatioA :
      (1 / (2 * (a : ℝ))) / (1 / ((a : ℝ) + b)) = ((a : ℝ) + b) / (2 * (a : ℝ)) := by
    field_simp [haR.ne', hbR.ne']
  have hRatioB :
      (1 / (2 * (b : ℝ))) / (1 / ((a : ℝ) + b)) = ((a : ℝ) + b) / (2 * (b : ℝ)) := by
    field_simp [haR.ne', hbR.ne']
  have hPosA : 0 < ((a : ℝ) + b) / (2 * (a : ℝ)) := by positivity
  have hPosB : 0 < ((a : ℝ) + b) / (2 * (b : ℝ)) := by positivity
  have hProd :
      (((a : ℝ) + b) / (2 * (a : ℝ))) * (((a : ℝ) + b) / (2 * (b : ℝ))) =
        (((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b) := by
    field_simp [haR.ne', hbR.ne']
    ring
  calc
    klDiv (sequentialUniformLift a b) (directUniformLift a b)
        = (a : ℝ) * (1 / (2 * (a : ℝ)) *
            Real.log ((1 / (2 * (a : ℝ))) / (1 / ((a : ℝ) + b)))) +
          (b : ℝ) * (1 / (2 * (b : ℝ)) *
            Real.log ((1 / (2 * (b : ℝ))) / (1 / ((a : ℝ) + b)))) := hsum
    _ = ((a : ℝ) * (1 / (2 * (a : ℝ)))) * Real.log ((1 / (2 * (a : ℝ))) / (1 / ((a : ℝ) + b))) +
          ((b : ℝ) * (1 / (2 * (b : ℝ)))) * Real.log ((1 / (2 * (b : ℝ))) / (1 / ((a : ℝ) + b))) := by
      ring
    _ = (1 / 2 : ℝ) * Real.log (((a : ℝ) + b) / (2 * (a : ℝ))) +
          (1 / 2 : ℝ) * Real.log (((a : ℝ) + b) / (2 * (b : ℝ))) := by
      rw [hHalfA, hHalfB, hRatioA, hRatioB]
    _ = (Real.log (((a : ℝ) + b) / (2 * (a : ℝ))) +
          Real.log (((a : ℝ) + b) / (2 * (b : ℝ)))) / 2 := by
      ring
    _ = (Real.log ((((a : ℝ) + b) / (2 * (a : ℝ))) *
          (((a : ℝ) + b) / (2 * (b : ℝ))))) / 2 := by
      rw [← Real.log_mul hPosA.ne' hPosB.ne']
    _ = twoFiberAmgmDefect a b := by
      rw [hProd, twoFiberAmgmDefect]

lemma entropy_gap_eq_twoFiberAmgmDefect (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    shannonEntropy (directUniformLift a b) - shannonEntropy (sequentialUniformLift a b) =
      twoFiberAmgmDefect a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  rw [shannonEntropy_directUniformLift a b ha hb, shannonEntropy_sequentialUniformLift a b ha hb]
  have hSumPos : 0 < (a : ℝ) + b := by positivity
  have hTwoAPos : 0 < 2 * (a : ℝ) := by positivity
  have hTwoBPos : 0 < 2 * (b : ℝ) := by positivity
  calc
    Real.log ((a : ℝ) + b) - (Real.log (2 * (a : ℝ)) + Real.log (2 * (b : ℝ))) / 2
        = (2 * Real.log ((a : ℝ) + b) -
            (Real.log (2 * (a : ℝ)) + Real.log (2 * (b : ℝ)))) / 2 := by
              ring
    _ = (Real.log (((a : ℝ) + b) ^ 2) - Real.log ((2 * (a : ℝ)) * (2 * (b : ℝ)))) / 2 := by
      rw [pow_two, Real.log_mul hSumPos.ne' hSumPos.ne', Real.log_mul hTwoAPos.ne' hTwoBPos.ne']
      ring
    _ = Real.log ((((a : ℝ) + b) ^ 2) / ((2 * (a : ℝ)) * (2 * (b : ℝ)))) / 2 := by
      rw [← Real.log_div (by positivity) (by positivity)]
    _ = twoFiberAmgmDefect a b := by
      congr 1
      field_simp [haR.ne', hbR.ne']
      ring_nf

lemma twoFiberAmgmDefect_eq_zero_iff (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    twoFiberAmgmDefect a b = 0 ↔ a = b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  constructor
  · intro h
    have hLog : Real.log ((((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b)) = 0 := by
      have hTwo := congrArg (fun t : ℝ => 2 * t) h
      simpa [twoFiberAmgmDefect] using hTwo
    have hPos : 0 < ((((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b)) := by positivity
    have hOne : ((((a : ℝ) + b) ^ 2) / (4 * (a : ℝ) * b)) = 1 := by
      have hExp := congrArg Real.exp hLog
      simpa [Real.exp_log hPos, hPos.ne'] using hExp
    have hMul : ((a : ℝ) + b) ^ 2 = 4 * (a : ℝ) * b := by
      simpa using (div_eq_iff (by positivity : (4 * (a : ℝ) * b) ≠ 0)).mp hOne
    have hEqR : (a : ℝ) = b := by
      nlinarith [hMul]
    exact_mod_cast hEqR
  · intro hab
    subst hab
    unfold twoFiberAmgmDefect
    have hRatio : ((((a : ℝ) + a) ^ 2) / (4 * (a : ℝ) * a)) = 1 := by
      field_simp [haR.ne']
      ring_nf
    rw [hRatio]
    norm_num

/-- In the two-fiber Beck-Chevalley model, the entropy defect agrees with the KL defect and both
collapse to the AM-GM defect of the two inner fiber cardinalities. The defect vanishes exactly
when the two inner fibers have the same cardinality.
    thm:pom-bc-amgm-defect-identity -/
theorem paper_pom_bc_amgm_defect_identity (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    shannonEntropy (directUniformLift a b) - shannonEntropy (sequentialUniformLift a b) =
      klDiv (sequentialUniformLift a b) (directUniformLift a b) ∧
    klDiv (sequentialUniformLift a b) (directUniformLift a b) = twoFiberAmgmDefect a b ∧
    (klDiv (sequentialUniformLift a b) (directUniformLift a b) = 0 ↔ a = b) := by
  refine ⟨?_, klDiv_sequential_direct a b ha hb, ?_⟩
  · rw [entropy_gap_eq_twoFiberAmgmDefect a b ha hb, klDiv_sequential_direct a b ha hb]
  · rw [klDiv_sequential_direct a b ha hb]
    exact twoFiberAmgmDefect_eq_zero_iff a b ha hb

/-- Escort log-sum potential `Φ(t) = log ((a^t + b^t) / 2)` in the concrete two-fiber model. -/
noncomputable def pom_bc_amgm_defect_escort_variance_energy_potential (a b : ℕ) (t : ℝ) : ℝ :=
  Real.log ((1 / 2 : ℝ) *
    (Real.exp (t * Real.log (a : ℝ)) + Real.exp (t * Real.log (b : ℝ))))

/-- Escort expectation of `log a_y` in the concrete two-fiber model. -/
noncomputable def pom_bc_amgm_defect_escort_variance_energy_mean (a b : ℕ) (t : ℝ) : ℝ :=
  ((Real.log (a : ℝ)) * Real.exp (t * Real.log (a : ℝ)) +
      (Real.log (b : ℝ)) * Real.exp (t * Real.log (b : ℝ))) /
    (Real.exp (t * Real.log (a : ℝ)) + Real.exp (t * Real.log (b : ℝ)))

/-- Escort variance of `log a_y` in the concrete two-fiber model. -/
noncomputable def pom_bc_amgm_defect_escort_variance_energy_variance
    (a b : ℕ) (t : ℝ) : ℝ :=
  (((Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (2 : ℕ)) *
      Real.exp (t * Real.log (a : ℝ)) * Real.exp (t * Real.log (b : ℝ))) /
    (Real.exp (t * Real.log (a : ℝ)) + Real.exp (t * Real.log (b : ℝ))) ^ (2 : ℕ)

/-- Paper label: `prop:pom-bc-amgm-defect-escort-variance-energy`. In the concrete two-fiber
model, the escort potential, the escort mean and variance at `t = 0`, and the endpoint remainder
recover the AM-GM defect energy. -/
theorem paper_pom_bc_amgm_defect_escort_variance_energy (a b : ℕ) (ha : 0 < a) (hb : 0 < b) :
    pom_bc_amgm_defect_escort_variance_energy_potential a b 0 = 0 ∧
    pom_bc_amgm_defect_escort_variance_energy_mean a b 0 =
      (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2 ∧
    pom_bc_amgm_defect_escort_variance_energy_variance a b 0 =
      ((Real.log (a : ℝ) - Real.log (b : ℝ)) ^ (2 : ℕ)) / 4 ∧
    pom_bc_amgm_defect_escort_variance_energy_potential a b 1 -
        pom_bc_amgm_defect_escort_variance_energy_mean a b 0 =
      twoFiberAmgmDefect a b := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  have hbR : 0 < (b : ℝ) := by exact_mod_cast hb
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [pom_bc_amgm_defect_escort_variance_energy_potential]
    norm_num
  · rw [pom_bc_amgm_defect_escort_variance_energy_mean]
    simp
    ring
  · rw [pom_bc_amgm_defect_escort_variance_energy_variance]
    simp [pow_two]
    ring
  · have hPotentialOne :
        pom_bc_amgm_defect_escort_variance_energy_potential a b 1 = Real.log (((a : ℝ) + b) / 2) := by
      rw [pom_bc_amgm_defect_escort_variance_energy_potential]
      simp only [one_mul]
      rw [Real.exp_log haR, Real.exp_log hbR]
      congr 1
      ring
    have hMeanZero : pom_bc_amgm_defect_escort_variance_energy_mean a b 0 =
        (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2 := by
      rw [pom_bc_amgm_defect_escort_variance_energy_mean]
      simp
      ring
    rw [hPotentialOne, hMeanZero]
    calc
      Real.log (((a : ℝ) + b) / 2) - (Real.log (a : ℝ) + Real.log (b : ℝ)) / 2
          = (2 * Real.log (((a : ℝ) + b) / 2) - (Real.log (a : ℝ) + Real.log (b : ℝ))) / 2 := by
              ring
      _ = (Real.log ((((a : ℝ) + b) / 2) ^ (2 : ℕ)) - Real.log ((a : ℝ) * b)) / 2 := by
        have hHalfPos : 0 < (((a : ℝ) + b) / 2) := by positivity
        rw [pow_two, Real.log_mul hHalfPos.ne' hHalfPos.ne', Real.log_mul haR.ne' hbR.ne']
        ring
      _ = Real.log (((((a : ℝ) + b) / 2) ^ (2 : ℕ)) / ((a : ℝ) * b)) / 2 := by
        rw [← Real.log_div (by positivity) (by positivity)]
      _ = twoFiberAmgmDefect a b := by
        unfold twoFiberAmgmDefect
        congr 1
        field_simp [haR.ne', hbR.ne']
        ring_nf

end

end Omega.POM
