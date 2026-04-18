import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity
import Omega.POM.MaxentLift

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

private lemma microstate_eq_zero_of_fiber_zero
    (d : X → ℕ) (mu : FiberMicrostate d → ℝ)
    (hmu_nonneg : ∀ a, 0 ≤ mu a)
    {x : X} (hx : fiberMarginal d mu x = 0) (i : Fin (d x)) :
    mu ⟨x, i⟩ = 0 := by
  have hle : mu ⟨x, i⟩ ≤ fiberMarginal d mu x := by
    simpa [fiberMarginal] using
      (Finset.single_le_sum (fun j _ => hmu_nonneg ⟨x, j⟩) (Finset.mem_univ i))
  have hnonneg : 0 ≤ mu ⟨x, i⟩ := hmu_nonneg ⟨x, i⟩
  rw [hx] at hle
  linarith

private lemma fiber_uniform_entropy_as_cross
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (pi : X → ℝ) (x : X) :
    fiberEntropy d (fiberUniformLift d pi) x = pi x * (-Real.log (pi x / d x)) := by
  have hd0 : (d x : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hd x))
  calc
    fiberEntropy d (fiberUniformLift d pi) x
        = (d x : ℝ) * Real.negMulLog (pi x / d x) := by
            simp [fiberEntropy, fiberUniformLift]
    _ = pi x * (-Real.log (pi x / d x)) := by
      rw [Real.negMulLog]
      field_simp [hd0]

/-- For a finite lifted distribution with the prescribed marginal, the KL divergence to the
fiber-uniform lift equals the corresponding entropy defect.
    prop:pom-kl-defect-identity -/
theorem paper_pom_kl_defect_identity {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (pi : X → ℝ) (mu : FiberMicrostate d → ℝ)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_nonneg : ∀ a, 0 ≤ mu a)
    (hpi_nonneg : ∀ x, 0 ≤ pi x) (hmu_sum : Finset.univ.sum mu = 1) :
    klDiv mu (fiberUniformLift d pi) = liftEntropy d (fiberUniformLift d pi) - liftEntropy d mu := by
  have hsplit :
      klDiv mu (fiberUniformLift d pi) =
        (∑ a, -Real.negMulLog (mu a)) +
          ∑ a, mu a * (-Real.log (fiberUniformLift d pi a)) := by
    unfold klDiv
    calc
      ∑ a, mu a * Real.log (mu a / fiberUniformLift d pi a)
          = ∑ a, (-Real.negMulLog (mu a) + mu a * (-Real.log (fiberUniformLift d pi a))) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              rcases a with ⟨x, i⟩
              by_cases hpi0 : pi x = 0
              · have hmu0 : mu ⟨x, i⟩ = 0 := by
                  have hx0 : fiberMarginal d mu x = 0 := by rw [hmu_marginal x, hpi0]
                  exact microstate_eq_zero_of_fiber_zero d mu hmu_nonneg hx0 i
                simp [fiberUniformLift, hpi0, hmu0]
              · have hq0 : fiberUniformLift d pi ⟨x, i⟩ ≠ 0 := by
                  simp [fiberUniformLift, hpi0, Nat.ne_of_gt (hd x)]
                by_cases hmu0 : mu ⟨x, i⟩ = 0
                · simp [hmu0]
                · rw [Real.negMulLog, Real.log_div hmu0 hq0]
                  ring
      _ = (∑ a, -Real.negMulLog (mu a)) + ∑ a, mu a * (-Real.log (fiberUniformLift d pi a)) := by
            rw [Finset.sum_add_distrib]
  have hnegEntropy : (∑ a, -Real.negMulLog (mu a)) = -liftEntropy d mu := by
    simp [liftEntropy, fiberEntropy, Fintype.sum_sigma]
  have hcross :
      ∑ a, mu a * (-Real.log (fiberUniformLift d pi a)) = liftEntropy d (fiberUniformLift d pi) := by
    rw [Fintype.sum_sigma, liftEntropy]
    refine Finset.sum_congr rfl ?_
    intro x hx
    calc
      ∑ i : Fin (d x), mu ⟨x, i⟩ * (-Real.log (fiberUniformLift d pi ⟨x, i⟩))
          = (∑ i : Fin (d x), mu ⟨x, i⟩) * (-Real.log (pi x / d x)) := by
              simp [fiberUniformLift, ← Finset.sum_mul]
      _ = fiberMarginal d mu x * (-Real.log (pi x / d x)) := by
            simp [fiberMarginal]
      _ = pi x * (-Real.log (pi x / d x)) := by rw [hmu_marginal x]
      _ = fiberEntropy d (fiberUniformLift d pi) x := by
            rw [fiber_uniform_entropy_as_cross d hd pi x]
  calc
    klDiv mu (fiberUniformLift d pi)
        = (∑ a, -Real.negMulLog (mu a)) + ∑ a, mu a * (-Real.log (fiberUniformLift d pi a)) := hsplit
    _ = -liftEntropy d mu + liftEntropy d (fiberUniformLift d pi) := by rw [hnegEntropy, hcross]
    _ = liftEntropy d (fiberUniformLift d pi) - liftEntropy d mu := by ring

end

end Omega.POM
