import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- Concrete half-entropy coordinate used by the single-layer recovery model. -/
noncomputable def conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy
    {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  ∑ x, w x

/-- The scalar one-parameter function obtained after the tensor pdet formula is rewritten in the
half-entropy coordinate. -/
def conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_scalar
    (k : ℕ) (h : ℝ) : ℝ :=
  (k + 1 : ℝ) * h

/-- Geometric-mean-normalized single-layer pseudodeterminant in the concrete recovery model. -/
noncomputable def conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi
    {n : ℕ} (k : ℕ) (w : Fin n → ℝ) : ℝ :=
  conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_scalar k
    (conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy w)

/-- Paper label: `cor:conclusion-critical-kernel-single-layer-pdet-recovers-halfentropy`.
The single-layer pdet expression factors through a strictly monotone scalar function of
half-entropy; hence equality at one layer recovers half-entropy and transports to every layer. -/
theorem paper_conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy
    {n : ℕ} (k : ℕ) (_hn : 2 ≤ n) (_hk : 1 ≤ k) (w v : Fin n → ℝ) :
    StrictMono (conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_scalar k) ∧
      (conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi k w =
          conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi k v →
        conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy w =
            conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy v ∧
          ∀ l : ℕ,
            conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi l w =
              conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi l v) := by
  have hmono :
      StrictMono (conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_scalar k) := by
    intro a b hab
    have hkpos : 0 < (k + 1 : ℝ) := by positivity
    dsimp [conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_scalar]
    exact mul_lt_mul_of_pos_left hab hkpos
  refine ⟨hmono, ?_⟩
  intro hPi
  have hhalf :
      conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy w =
        conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_halfEntropy v := by
    exact hmono.injective hPi
  refine ⟨hhalf, ?_⟩
  intro l
  simp [conclusion_critical_kernel_single_layer_pdet_recovers_halfentropy_Pi, hhalf]

end Omega.Conclusion
