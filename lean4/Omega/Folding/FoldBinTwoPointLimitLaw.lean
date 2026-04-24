import Mathlib
import Mathlib.Tactic
import Omega.Folding.Entropy
import Omega.Folding.FoldBinTwoStateAsymptotic

namespace Omega.Folding

/-- The cardinality of the last-bit class in the two-state bin-fold model. -/
def foldBinLastBitClassMass (m : ℕ) (b : Bool) : ℕ :=
  if b then Nat.fib m else Nat.fib (m + 1)

/-- The scaled two-atom model read off from the last bit. -/
noncomputable def foldBinScaledTwoAtomModel (b : Bool) : ℝ :=
  foldBinTwoStateWeight b

/-- Limiting masses of the two-atom model. -/
noncomputable def foldBinTwoAtomLimitMass (b : Bool) : ℝ :=
  if b then 1 / (Real.goldenRatio * Real.sqrt 5) else Real.goldenRatio / Real.sqrt 5

/-- Paper-facing formulation of the bin-fold two-point limit law: the two-state asymptotic package
is inherited from the existing model, the terminal-state classes have Fibonacci sizes, the scaled
two-atom model is exactly the last-bit weight, and the class masses converge to the claimed two
probabilities. -/
def paper_fold_bin_two_point_limit_law_statement (D : FoldBinTwoStateAsymptoticData) : Prop :=
  D.uniform_two_state_asymptotic ∧
    (∀ m, foldBinLastBitClassMass m false = Nat.fib (m + 1)) ∧
    (∀ m, foldBinLastBitClassMass m true = Nat.fib m) ∧
    (∀ b, foldBinScaledTwoAtomModel b = foldBinTwoStateWeight b) ∧
    Filter.Tendsto
      (fun m : ℕ => (foldBinLastBitClassMass m false : ℝ) * Real.goldenRatio ^ (-(m : ℝ)))
      Filter.atTop (nhds (Real.goldenRatio / Real.sqrt 5)) ∧
    Filter.Tendsto
      (fun m : ℕ => (foldBinLastBitClassMass m true : ℝ) * Real.goldenRatio ^ (-(m : ℝ)))
      Filter.atTop (nhds ((Real.sqrt 5)⁻¹)) ∧
    foldBinTwoAtomLimitMass false = Real.goldenRatio / Real.sqrt 5 ∧
    foldBinTwoAtomLimitMass true = 1 / (Real.goldenRatio * Real.sqrt 5) ∧
    foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true = 1

private lemma foldBinLastBitClassMass_zero_tendsto :
    Filter.Tendsto
      (fun m : ℕ => (foldBinLastBitClassMass m false : ℝ) * Real.goldenRatio ^ (-(m : ℝ)))
      Filter.atTop (nhds (Real.goldenRatio / Real.sqrt 5)) := by
  have hshift :
      Filter.Tendsto
        (fun m : ℕ => (Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹)
        Filter.atTop (nhds ((Real.sqrt 5)⁻¹)) := by
    have hshift0 :=
      Filter.Tendsto.comp Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5
        (Filter.tendsto_add_atTop_nat 1)
    simpa [Function.comp] using hshift0
  have hEq :
      (fun m : ℕ => (foldBinLastBitClassMass m false : ℝ) * Real.goldenRatio ^ (-(m : ℝ))) =ᶠ[Filter.atTop]
        fun m : ℕ =>
          Real.goldenRatio * ((Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹) :=
    Filter.Eventually.of_forall fun m => by
      calc
        (foldBinLastBitClassMass m false : ℝ) * Real.goldenRatio ^ (-(m : ℝ)) =
            (Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ)) := by
              simp [foldBinLastBitClassMass]
        _ = Real.goldenRatio * ((Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹) := by
              have hpow :
                  Real.goldenRatio ^ (-(m : ℝ)) =
                    Real.goldenRatio * (Real.goldenRatio ^ (m + 1))⁻¹ := by
                rw [Real.rpow_neg Real.goldenRatio_pos.le, Real.rpow_natCast]
                field_simp [pow_ne_zero (m + 1) Real.goldenRatio_ne_zero]
                ring
              calc
                (Nat.fib (m + 1) : ℝ) * Real.goldenRatio ^ (-(m : ℝ)) =
                    (Nat.fib (m + 1) : ℝ) *
                      (Real.goldenRatio * (Real.goldenRatio ^ (m + 1))⁻¹) := by
                        rw [hpow]
                _ = Real.goldenRatio * ((Nat.fib (m + 1) : ℝ) * (Real.goldenRatio ^ (m + 1))⁻¹) := by
                    ring
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa [one_div, mul_comm, mul_left_comm, mul_assoc] using hshift.const_mul Real.goldenRatio

private lemma foldBinLastBitClassMass_one_tendsto :
    Filter.Tendsto
      (fun m : ℕ => (foldBinLastBitClassMass m true : ℝ) * Real.goldenRatio ^ (-(m : ℝ)))
      Filter.atTop (nhds ((Real.sqrt 5)⁻¹)) := by
  have hEq :
      (fun m : ℕ => (foldBinLastBitClassMass m true : ℝ) * Real.goldenRatio ^ (-(m : ℝ))) =ᶠ[Filter.atTop]
        fun m : ℕ => (Nat.fib m : ℝ) * Real.goldenRatio ^ (-(m : ℝ)) := by
    exact Filter.Eventually.of_forall fun m => by simp [foldBinLastBitClassMass]
  refine Filter.Tendsto.congr' hEq.symm ?_
  simpa [one_div, mul_assoc, mul_left_comm, mul_comm] using
    Omega.Entropy.fib_mul_phi_neg_tendsto_inv_sqrt5

private lemma foldBinTwoAtomLimitMass_sum :
    foldBinTwoAtomLimitMass false + foldBinTwoAtomLimitMass true = 1 := by
  have hsqrt5_ne : (Real.sqrt 5 : ℝ) ≠ 0 := by
    have hsqrt5_pos : 0 < Real.sqrt 5 := by positivity
    exact ne_of_gt hsqrt5_pos
  have hphi_ne : Real.goldenRatio ≠ 0 := Real.goldenRatio_ne_zero
  have hphi :
      Real.goldenRatio + Real.goldenRatio⁻¹ = Real.sqrt 5 := by
    rw [Real.inv_goldenRatio]
    linarith [Real.goldenRatio_sub_goldenConj]
  unfold foldBinTwoAtomLimitMass
  change Real.goldenRatio / Real.sqrt 5 + 1 / (Real.goldenRatio * Real.sqrt 5) = 1
  calc
    Real.goldenRatio / Real.sqrt 5 + 1 / (Real.goldenRatio * Real.sqrt 5) =
        (Real.goldenRatio + Real.goldenRatio⁻¹) / Real.sqrt 5 := by
          field_simp [hsqrt5_ne, hphi_ne]
    _ = Real.sqrt 5 / Real.sqrt 5 := by rw [hphi]
    _ = 1 := by field_simp [hsqrt5_ne]

/-- Paper-facing two-point convergence law for the bin-fold two-state model.
    cor:fold-bin-two-point-limit-law -/
theorem paper_fold_bin_two_point_limit_law (D : FoldBinTwoStateAsymptoticData) :
    paper_fold_bin_two_point_limit_law_statement D := by
  refine ⟨paper_fold_bin_two_state_asymptotic D, ?_, ?_, ?_, ?_, ?_, rfl, rfl,
    foldBinTwoAtomLimitMass_sum⟩
  · intro m
    simp [foldBinLastBitClassMass]
  · intro m
    simp [foldBinLastBitClassMass]
  · intro b
    rfl
  · exact foldBinLastBitClassMass_zero_tendsto
  · exact foldBinLastBitClassMass_one_tendsto

end Omega.Folding
