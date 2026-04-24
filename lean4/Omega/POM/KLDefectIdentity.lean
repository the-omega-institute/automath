import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity
import Omega.POM.MaxentLift

namespace Omega.POM

open scoped BigOperators

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The conditional law on the explicit fiber above `x`, obtained by normalizing `μ` by the
fiber mass `π x` and set to zero on empty fibers. -/
noncomputable def fiberConditionalLaw
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (x : X) : Fin (d x) → ℝ :=
  fun i => if _h : π x = 0 then 0 else μ ⟨x, i⟩ / π x

/-- The uniform law on the explicit fiber above `x`. -/
noncomputable def fiberUniformLaw (d : X → ℕ) (x : X) : Fin (d x) → ℝ :=
  fun _ => 1 / d x

/-- Shannon entropy of the fiber-conditional law. -/
noncomputable def fiberConditionalEntropy
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) (x : X) : ℝ :=
  ∑ i : Fin (d x), Real.negMulLog (fiberConditionalLaw d π μ x i)

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

private lemma fiberConditionalLaw_mul_pi
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ) {x : X} (hπ : π x ≠ 0)
    (i : Fin (d x)) :
    π x * fiberConditionalLaw d π μ x i = μ ⟨x, i⟩ := by
  simp [fiberConditionalLaw, hπ]
  field_simp [hπ]

private lemma fiberUniformLift_mul_uniformLaw
    (d : X → ℕ) (π : X → ℝ) (x : X) (i : Fin (d x)) :
    π x * fiberUniformLaw d x i = fiberUniformLift d π ⟨x, i⟩ := by
  simp [fiberUniformLaw, fiberUniformLift]
  ring

private lemma fiberConditionalLaw_sum
    (d : X → ℕ) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) {x : X} (hπ : π x ≠ 0) :
    ∑ i : Fin (d x), fiberConditionalLaw d π μ x i = 1 := by
  calc
    ∑ i : Fin (d x), fiberConditionalLaw d π μ x i
        = ∑ i : Fin (d x), μ ⟨x, i⟩ / π x := by
            refine Finset.sum_congr rfl ?_
            intro i hi
            simp [fiberConditionalLaw, hπ]
    _ = (∑ i : Fin (d x), μ ⟨x, i⟩) / π x := by
          rw [Finset.sum_div]
    _ = fiberMarginal d μ x / π x := by
          simp [fiberMarginal]
    _ = π x / π x := by rw [hμ_marginal x]
    _ = 1 := by field_simp [hπ]

private lemma fiberConditionalLaw_kl_to_uniform
    (d : X → ℕ) (hd : ∀ x, 0 < d x) (π : X → ℝ) (μ : FiberMicrostate d → ℝ)
    (hμ_marginal : ∀ x, fiberMarginal d μ x = π x) {x : X} (hπ : π x ≠ 0) :
    klDiv (fiberConditionalLaw d π μ x) (fiberUniformLaw d x) =
      Real.log (d x) - fiberConditionalEntropy d π μ x := by
  have hd0 : (d x : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (hd x))
  have hsum : ∑ i : Fin (d x), fiberConditionalLaw d π μ x i = 1 :=
    fiberConditionalLaw_sum d π μ hμ_marginal hπ
  have hsplit :
      klDiv (fiberConditionalLaw d π μ x) (fiberUniformLaw d x) =
        (∑ i : Fin (d x), -Real.negMulLog (fiberConditionalLaw d π μ x i)) +
          ∑ i : Fin (d x), fiberConditionalLaw d π μ x i * Real.log (d x) := by
    unfold klDiv
    calc
      ∑ i : Fin (d x),
          fiberConditionalLaw d π μ x i *
            Real.log (fiberConditionalLaw d π μ x i / fiberUniformLaw d x i)
          =
            ∑ i : Fin (d x),
              (-Real.negMulLog (fiberConditionalLaw d π μ x i) +
                fiberConditionalLaw d π μ x i * Real.log (d x)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              by_cases hμ0 : fiberConditionalLaw d π μ x i = 0
              · simp [hμ0, fiberUniformLaw]
              · have hratio :
                    fiberConditionalLaw d π μ x i / fiberUniformLaw d x i =
                      fiberConditionalLaw d π μ x i * d x := by
                  calc
                    fiberConditionalLaw d π μ x i / fiberUniformLaw d x i
                        = fiberConditionalLaw d π μ x i / (1 / d x) := by
                            simp [fiberUniformLaw]
                    _ = fiberConditionalLaw d π μ x i * d x := by
                          field_simp [hd0]
                rw [hratio, Real.log_mul hμ0 hd0, Real.negMulLog]
                ring
      _ = (∑ i : Fin (d x), -Real.negMulLog (fiberConditionalLaw d π μ x i)) +
            ∑ i : Fin (d x), fiberConditionalLaw d π μ x i * Real.log (d x) := by
              rw [Finset.sum_add_distrib]
  calc
    klDiv (fiberConditionalLaw d π μ x) (fiberUniformLaw d x)
        = (∑ i : Fin (d x), -Real.negMulLog (fiberConditionalLaw d π μ x i)) +
            ∑ i : Fin (d x), fiberConditionalLaw d π μ x i * Real.log (d x) := hsplit
    _ = -fiberConditionalEntropy d π μ x +
          ∑ i : Fin (d x), fiberConditionalLaw d π μ x i * Real.log (d x) := by
            simp [fiberConditionalEntropy]
    _ = -fiberConditionalEntropy d π μ x +
          (∑ i : Fin (d x), fiberConditionalLaw d π μ x i) * Real.log (d x) := by
            rw [← Finset.sum_mul]
    _ = Real.log (d x) - fiberConditionalEntropy d π μ x := by
            rw [hsum]
            ring

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

/-- Closed-form paper ledger: visible entropy plus fiber capacity minus the KL defect to the
fiber-uniform lift.
    thm:pom-kl-ledger -/
theorem paper_pom_kl_ledger {X : Type*} [Fintype X] [DecidableEq X] (d : X -> Nat)
    (hd : forall x, 0 < d x) (pi : X -> Real) (mu : FiberMicrostate d -> Real)
    (hmu_marginal : forall x, fiberMarginal d mu x = pi x) (hmu_nonneg : forall a, 0 <= mu a)
    (hpi_nonneg : forall x, 0 <= pi x) (hmu_sum : Finset.univ.sum mu = 1) :
    liftEntropy d mu = (Finset.univ.sum fun x : X => Real.negMulLog (pi x)) +
      Finset.univ.sum (fun x : X => pi x * Real.log (d x)) - klDiv mu (fiberUniformLift d pi) := by
  have hdefect :=
    paper_pom_kl_defect_identity d hd pi mu hmu_marginal hmu_nonneg hpi_nonneg hmu_sum
  have huniform :
      liftEntropy d (fiberUniformLift d pi) =
        (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) := by
    exact
      (paper_pom_maxent_lift d hd pi (fiberUniformLift d pi)
        (by intro x i j; rfl)
        (by
          intro x
          have hd0 : (d x : ℝ) ≠ 0 := by
            exact_mod_cast (Nat.ne_of_gt (hd x))
          calc
            fiberMarginal d (fiberUniformLift d pi) x = ∑ _i : Fin (d x), pi x / d x := by
              simp [fiberMarginal, fiberUniformLift]
            _ = (d x : ℝ) * (pi x / d x) := by simp
            _ = pi x := by field_simp [hd0])).2
  calc
    liftEntropy d mu
        = liftEntropy d (fiberUniformLift d pi) - klDiv mu (fiberUniformLift d pi) := by
            linarith [hdefect]
    _ = (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) -
          klDiv mu (fiberUniformLift d pi) := by rw [huniform]

/-- Paper-facing ledger bound: among all lifts with the same marginal, the fiber-uniform lift
attains the entropy upper bound, and equality forces fiberwise uniformity.
    cor:pom-kl-ledger-bound -/
theorem paper_pom_kl_ledger_bound {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (pi : X → ℝ) (mu : FiberMicrostate d → ℝ)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_nonneg : ∀ a, 0 ≤ mu a)
    (hpi_nonneg : ∀ x, 0 ≤ pi x) (hmu_sum : Finset.univ.sum mu = 1)
    (hkl_nonneg : 0 ≤ klDiv mu (fiberUniformLift d pi))
    (hkl_zero_iff : klDiv mu (fiberUniformLift d pi) = 0 ↔ mu = fiberUniformLift d pi) :
    liftEntropy d mu ≤
        (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) ∧
      (liftEntropy d mu =
          (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) ↔
        FiberwiseUniform d mu) := by
  have hledger := paper_pom_kl_defect_identity d hd pi mu hmu_marginal hmu_nonneg hpi_nonneg hmu_sum
  have hUniformMarginal : ∀ x, fiberMarginal d (fiberUniformLift d pi) x = pi x := by
    intro x
    have hd0 : (d x : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hd x))
    calc
      fiberMarginal d (fiberUniformLift d pi) x = ∑ _i : Fin (d x), pi x / d x := by
        simp [fiberMarginal, fiberUniformLift]
      _ = (d x : ℝ) * (pi x / d x) := by simp
      _ = pi x := by
        field_simp [hd0]
  have hUniformEntropy :
      liftEntropy d (fiberUniformLift d pi) =
        (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) := by
    exact
      (paper_pom_maxent_lift d hd pi (fiberUniformLift d pi)
        (by intro x i j; rfl) hUniformMarginal).2
  have hUpper : liftEntropy d mu ≤ liftEntropy d (fiberUniformLift d pi) := by
    have hgap_nonneg : 0 ≤ liftEntropy d (fiberUniformLift d pi) - liftEntropy d mu := by
      rw [← hledger]
      exact hkl_nonneg
    linarith
  refine ⟨by simpa [hUniformEntropy] using hUpper, ?_⟩
  constructor
  · intro hEq
    have hLiftEq : liftEntropy d mu = liftEntropy d (fiberUniformLift d pi) := by
      calc
        liftEntropy d mu =
            (∑ x : X, Real.negMulLog (pi x)) + ∑ x : X, pi x * Real.log (d x) := hEq
        _ = liftEntropy d (fiberUniformLift d pi) := hUniformEntropy.symm
    have hkl_zero : klDiv mu (fiberUniformLift d pi) = 0 := by
      rw [hledger, hLiftEq]
      ring
    have hmu_eq : mu = fiberUniformLift d pi := hkl_zero_iff.mp hkl_zero
    intro x i j
    simpa [hmu_eq, fiberUniformLift]
  · intro hFiberwise
    have hmu_eq : mu = fiberUniformLift d pi :=
      (paper_pom_maxent_lift d hd pi mu hFiberwise hmu_marginal).1
    rw [hmu_eq, hUniformEntropy]

/-- Fiberwise chain rule for the KL defect to the fiber-uniform lift: each fiber contributes its
visible mass times the conditional KL divergence to the uniform law on that fiber.
    lem:pom-fiberwise-kl -/
theorem paper_pom_fiberwise_kl {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (pi : X → ℝ) (mu : FiberMicrostate d → ℝ)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_nonneg : ∀ a, 0 ≤ mu a) :
    klDiv mu (fiberUniformLift d pi) =
      ∑ x : X, pi x * klDiv (fiberConditionalLaw d pi mu x) (fiberUniformLaw d x) := by
  rw [klDiv, Fintype.sum_sigma]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases hpi0 : pi x = 0
  · have hx0 : fiberMarginal d mu x = 0 := by simpa [hpi0] using hmu_marginal x
    have hmu0 : ∀ i : Fin (d x), mu ⟨x, i⟩ = 0 := by
      intro i
      exact microstate_eq_zero_of_fiber_zero d mu hmu_nonneg hx0 i
    simp [hpi0, hmu0, fiberConditionalLaw, fiberUniformLift]
  · have hd0 : (d x : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt (hd x))
    calc
      ∑ i : Fin (d x), mu ⟨x, i⟩ * Real.log (mu ⟨x, i⟩ / fiberUniformLift d pi ⟨x, i⟩)
          = ∑ i : Fin (d x),
              pi x *
                (fiberConditionalLaw d pi mu x i *
                  Real.log (fiberConditionalLaw d pi mu x i / fiberUniformLaw d x i)) := by
              refine Finset.sum_congr rfl ?_
              intro i hi
              have hμ :
                  pi x * fiberConditionalLaw d pi mu x i = mu ⟨x, i⟩ :=
                fiberConditionalLaw_mul_pi d pi mu hpi0 i
              have hratio :
                  mu ⟨x, i⟩ / fiberUniformLift d pi ⟨x, i⟩ =
                    fiberConditionalLaw d pi mu x i / fiberUniformLaw d x i := by
                simp [fiberConditionalLaw, fiberUniformLaw, fiberUniformLift, hpi0]
                field_simp [hpi0, hd0]
              rw [hratio, ← hμ]
              ring
      _ = pi x * ∑ i : Fin (d x),
            fiberConditionalLaw d pi mu x i *
              Real.log (fiberConditionalLaw d pi mu x i / fiberUniformLaw d x i) := by
            rw [Finset.mul_sum]
      _ = pi x * klDiv (fiberConditionalLaw d pi mu x) (fiberUniformLaw d x) := by
            simp [klDiv]

/-- Explicit fiber-entropy-deficit form of the KL defect to the fiber-uniform lift.
    cor:pom-fiber-entropy-deficit -/
theorem paper_pom_fiber_entropy_deficit {X : Type*} [Fintype X] [DecidableEq X] (d : X → ℕ)
    (hd : ∀ x, 0 < d x) (pi : X → ℝ) (mu : FiberMicrostate d → ℝ)
    (hmu_marginal : ∀ x, fiberMarginal d mu x = pi x) (hmu_nonneg : ∀ a, 0 ≤ mu a) :
    klDiv mu (fiberUniformLift d pi) =
      ∑ x : X, pi x * (Real.log (d x) - fiberConditionalEntropy d pi mu x) := by
  rw [paper_pom_fiberwise_kl d hd pi mu hmu_marginal hmu_nonneg]
  refine Finset.sum_congr rfl ?_
  intro x hx
  by_cases hpi0 : pi x = 0
  · simp [hpi0]
  · rw [fiberConditionalLaw_kl_to_uniform d hd pi mu hmu_marginal hpi0]

end

end Omega.POM
