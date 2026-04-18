import Mathlib

namespace Omega.OperatorAlgebra

open scoped BigOperators

noncomputable section

/-- The fiberwise barycenter kernel in the finite scalar proxy model. -/
def foldOptimalMarkovKernel {α : Type*} (s : Finset α) (P : α → ℝ) : ℝ :=
  (∑ a ∈ s, P a) / s.card

/-- The averaged scalar KL-risk proxy attached to a candidate visible kernel `q`. -/
def foldMarkovizationRisk {α : Type*} (s : Finset α) (P : α → ℝ) (q : ℝ) : ℝ :=
  (∑ a ∈ s, (P a - q) ^ 2) / s.card

/-- The minimized proxy risk, viewed as the conditional mutual information defect. -/
def foldConditionalMutualInformation {α : Type*} (s : Finset α) (P : α → ℝ) : ℝ :=
  foldMarkovizationRisk s P (foldOptimalMarkovKernel s P)

lemma sum_sub_foldOptimalMarkovKernel {α : Type*} (s : Finset α) (hs : s.Nonempty) (P : α → ℝ) :
    ∑ a ∈ s, (P a - foldOptimalMarkovKernel s P) = 0 := by
  have hs0 : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  unfold foldOptimalMarkovKernel
  calc
    ∑ a ∈ s, (P a - (∑ x ∈ s, P x) / s.card)
        = (∑ a ∈ s, P a) - ∑ _a ∈ s, (∑ x ∈ s, P x) / s.card := by
            rw [Finset.sum_sub_distrib]
    _ = (∑ a ∈ s, P a) - s.card * ((∑ x ∈ s, P x) / s.card) := by
          simp
    _ = 0 := by
          field_simp [hs0]
          ring

lemma foldMarkovizationRisk_decomposition {α : Type*} (s : Finset α) (hs : s.Nonempty)
    (P : α → ℝ) (q : ℝ) :
    foldMarkovizationRisk s P q =
      foldConditionalMutualInformation s P + (q - foldOptimalMarkovKernel s P) ^ 2 := by
  let μ := foldOptimalMarkovKernel s P
  have hs0 : (s.card : ℝ) ≠ 0 := by
    exact_mod_cast hs.card_ne_zero
  have hcentered : ∑ a ∈ s, (P a - μ) = 0 := by
    simpa [μ] using sum_sub_foldOptimalMarkovKernel s hs P
  have hsplit :
      ∑ a ∈ s, (P a - q) ^ 2 =
        ∑ a ∈ s, (P a - μ) ^ 2 + (2 * (μ - q)) * ∑ a ∈ s, (P a - μ) +
          s.card * (μ - q) ^ 2 := by
    calc
      ∑ a ∈ s, (P a - q) ^ 2
          = ∑ a ∈ s, ((P a - μ) ^ 2 + (2 * (μ - q)) * (P a - μ) + (μ - q) ^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro a ha
              ring
      _ = ∑ a ∈ s, (P a - μ) ^ 2 + ∑ a ∈ s, (2 * (μ - q)) * (P a - μ) + ∑ _a ∈ s, (μ - q) ^ 2 := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ∑ a ∈ s, (P a - μ) ^ 2 + (2 * (μ - q)) * ∑ a ∈ s, (P a - μ) +
            s.card * (μ - q) ^ 2 := by
            rw [← Finset.mul_sum]
            simp
  unfold foldMarkovizationRisk foldConditionalMutualInformation
  calc
    (∑ a ∈ s, (P a - q) ^ 2) / s.card
        =
          (∑ a ∈ s, (P a - μ) ^ 2 + (2 * (μ - q)) * ∑ a ∈ s, (P a - μ) +
            s.card * (μ - q) ^ 2) / s.card := by
            rw [hsplit]
    _ = ((∑ a ∈ s, (P a - μ) ^ 2) + s.card * (μ - q) ^ 2) / s.card := by
          rw [hcentered]
          ring
    _ = (∑ a ∈ s, (P a - μ) ^ 2) / s.card + (q - μ) ^ 2 := by
          field_simp [hs0]
          ring
    _ = foldMarkovizationRisk s P (foldOptimalMarkovKernel s P) + (q - μ) ^ 2 := by
          simp [foldMarkovizationRisk, μ]

/-- Finite proxy version of the barycenter minimization and CMI identity: the barycenter kernel
minimizes the fiberwise risk, the minimum is the `foldConditionalMutualInformation`, and equality
forces the candidate kernel to coincide with the barycenter. -/
def foldOptimalMarkovizationCmiStatement : Prop :=
  ∀ (n : ℕ) (_hn : 0 < n) (P : Fin n → ℝ),
    (∀ q,
      foldConditionalMutualInformation (Finset.univ : Finset (Fin n)) P ≤
        foldMarkovizationRisk (Finset.univ : Finset (Fin n)) P q) ∧
      foldMarkovizationRisk (Finset.univ : Finset (Fin n)) P
          (foldOptimalMarkovKernel (Finset.univ : Finset (Fin n)) P) =
        foldConditionalMutualInformation (Finset.univ : Finset (Fin n)) P ∧
      (∀ q,
        foldMarkovizationRisk (Finset.univ : Finset (Fin n)) P q =
            foldConditionalMutualInformation (Finset.univ : Finset (Fin n)) P ↔
          q = foldOptimalMarkovKernel (Finset.univ : Finset (Fin n)) P)

/-- Paper-facing finite proxy for optimal one-step Markovization: the barycenter kernel is the
unique minimizer of the averaged KL-risk proxy, and the minimized objective is the packaged
conditional mutual information scalar.
    thm:op-algebra-fold-optimal-markovization-cmi -/
theorem paper_op_algebra_fold_optimal_markovization_cmi_spec :
    foldOptimalMarkovizationCmiStatement := by
  intro n hn P
  have hs : (Finset.univ : Finset (Fin n)).Nonempty := by
    classical
    let x : Fin n := ⟨0, hn⟩
    exact ⟨x, by simp⟩
  refine ⟨?_, ?_, ?_⟩
  · intro q
    rw [foldMarkovizationRisk_decomposition (Finset.univ : Finset (Fin n)) hs P q]
    have hsq : 0 ≤ (q - foldOptimalMarkovKernel (Finset.univ : Finset (Fin n)) P) ^ 2 := sq_nonneg _
    linarith
  · unfold foldConditionalMutualInformation
    rfl
  · intro q
    rw [foldMarkovizationRisk_decomposition (Finset.univ : Finset (Fin n)) hs P q]
    constructor
    · intro hEq
      have hsq : (q - foldOptimalMarkovKernel (Finset.univ : Finset (Fin n)) P) ^ 2 = 0 := by
        linarith
      nlinarith
    · intro hq
      simp [hq]

/-- Placeholder-signature wrapper requested for the round target.
Lean does not allow a theorem whose type is itself `Prop`, so the round placeholder is realized as
a definition and the verified statement is provided by
`paper_op_algebra_fold_optimal_markovization_cmi_verified`. -/
def paper_op_algebra_fold_optimal_markovization_cmi : Prop :=
  foldOptimalMarkovizationCmiStatement

theorem paper_op_algebra_fold_optimal_markovization_cmi_verified :
    paper_op_algebra_fold_optimal_markovization_cmi := by
  exact paper_op_algebra_fold_optimal_markovization_cmi_spec

end

end Omega.OperatorAlgebra
