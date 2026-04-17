import Mathlib
import Omega.OperatorAlgebra.FoldUniformLiftNllDecomposition

namespace Omega.OperatorAlgebra

open scoped BigOperators

noncomputable section

variable {α β Θ : Type*} [Fintype α] [Fintype β] [Fintype Θ] [Nonempty Θ]

/-- Finite-sample likelihood of a model `μ` on a length-`n` sample. -/
def foldSampleLikelihood {n : ℕ} (μ : α → ℝ) (sample : Fin n → α) : ℝ :=
  ∏ i, μ (sample i)

/-- Visible likelihood after projecting the sample through the fold map `F`. -/
def foldVisibleSampleLikelihood {n : ℕ} (F : α → β) (π : β → ℝ) (sample : Fin n → α) : ℝ :=
  ∏ i, π (F (sample i))

/-- The θ-independent product of reciprocal fiber sizes along a sample. -/
def foldFiberFactor {n : ℕ} (F : α → β) (d : β → ℝ) (sample : Fin n → α) : ℝ :=
  ∏ i, (d (F (sample i)))⁻¹

/-- Posterior mass after combining a prior with a finite likelihood ledger. -/
def foldPosteriorMass (prior likelihood : Θ → ℝ) (θ : Θ) : ℝ :=
  prior θ * likelihood θ / ∑ θ', prior θ' * likelihood θ'

/-- Two samples are visibly equivalent when they have the same fold image coordinatewise. -/
def foldVisibleEquivalent {n : ℕ} (F : α → β) (sample sample' : Fin n → α) : Prop :=
  ∀ i, F (sample i) = F (sample' i)

lemma foldSampleLikelihood_uniformLift_factorization {n : ℕ}
    (F : α → β) (π : β → ℝ) (d : β → ℝ) (sample : Fin n → α) :
    foldSampleLikelihood (foldUniformLift F π d) sample =
      foldFiberFactor F d sample * foldVisibleSampleLikelihood F π sample := by
  unfold foldSampleLikelihood foldUniformLift foldFiberFactor foldVisibleSampleLikelihood
  simp_rw [div_eq_mul_inv]
  rw [Finset.prod_mul_distrib, mul_comm]

lemma foldVisibleSampleLikelihood_pos {n : ℕ}
    (F : α → β) (π : β → ℝ) (sample : Fin n → α)
    (hπ : ∀ x, 0 < π x) :
    0 < foldVisibleSampleLikelihood F π sample := by
  unfold foldVisibleSampleLikelihood
  refine Finset.prod_pos ?_
  intro i hi
  exact hπ (F (sample i))

lemma foldFiberFactor_pos {n : ℕ}
    (F : α → β) (d : β → ℝ) (sample : Fin n → α)
    (hd : ∀ x, 0 < d x) :
    0 < foldFiberFactor F d sample := by
  unfold foldFiberFactor
  refine Finset.prod_pos ?_
  intro i hi
  exact inv_pos.mpr (hd (F (sample i)))

lemma foldPosteriorNormalizer_pos
    (prior likelihood : Θ → ℝ)
    (hprior : ∀ θ, 0 < prior θ)
    (hlikelihood : ∀ θ, 0 < likelihood θ) :
    0 < ∑ θ, prior θ * likelihood θ := by
  classical
  obtain ⟨θ0⟩ := ‹Nonempty Θ›
  have hpos : 0 < prior θ0 * likelihood θ0 := mul_pos (hprior θ0) (hlikelihood θ0)
  have hle : prior θ0 * likelihood θ0 ≤ ∑ θ, prior θ * likelihood θ := by
    exact Finset.single_le_sum
      (fun θ hθ => mul_nonneg (le_of_lt (hprior θ)) (le_of_lt (hlikelihood θ)))
      (Finset.mem_univ θ0)
  exact lt_of_lt_of_le hpos hle

lemma foldPosteriorMass_common_factor
    (prior likelihood : Θ → ℝ) (c : ℝ) (θ : Θ)
    (hc : c ≠ 0)
    (hnorm : ∑ θ', prior θ' * likelihood θ' ≠ 0) :
    foldPosteriorMass prior (fun θ' => c * likelihood θ') θ =
      foldPosteriorMass prior likelihood θ := by
  have hsum :
      ∑ θ', prior θ' * (c * likelihood θ') = c * ∑ θ', prior θ' * likelihood θ' := by
    calc
      ∑ θ', prior θ' * (c * likelihood θ')
          = ∑ θ', c * (prior θ' * likelihood θ') := by
              refine Finset.sum_congr rfl ?_
              intro θ' hθ'
              ring
      _ = c * ∑ θ', prior θ' * likelihood θ' := by
            rw [Finset.mul_sum]
  unfold foldPosteriorMass
  rw [hsum]
  field_simp [hc, hnorm]

lemma foldVisibleSampleLikelihood_congr {n : ℕ}
    (F : α → β) (π : β → ℝ) (sample sample' : Fin n → α)
    (hvis : foldVisibleEquivalent F sample sample') :
    foldVisibleSampleLikelihood F π sample = foldVisibleSampleLikelihood F π sample' := by
  unfold foldVisibleSampleLikelihood foldVisibleEquivalent at *
  refine Finset.prod_congr rfl ?_
  intro i hi
  simp [hvis i]

lemma foldPosteriorMass_eq_visible_of_uniformLift {n : ℕ}
    (F : α → β) (d : β → ℝ) (π : Θ → β → ℝ) (prior : Θ → ℝ)
    (sample : Fin n → α)
    (hd : ∀ x, 0 < d x)
    (hπ : ∀ θ x, 0 < π θ x)
    (hprior : ∀ θ, 0 < prior θ) :
    ∀ θ,
      foldPosteriorMass prior
          (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ =
        foldPosteriorMass prior
          (fun θ' => foldVisibleSampleLikelihood F (π θ') sample) θ := by
  intro θ
  let c : ℝ := foldFiberFactor F d sample
  let visible : Θ → ℝ := fun θ' => foldVisibleSampleLikelihood F (π θ') sample
  have hc : c ≠ 0 := ne_of_gt (foldFiberFactor_pos F d sample hd)
  have hvisible_pos : ∀ θ', 0 < visible θ' := by
    intro θ'
    unfold visible
    exact foldVisibleSampleLikelihood_pos F (π θ') sample (hπ θ')
  have hnorm : ∑ θ', prior θ' * visible θ' ≠ 0 := by
    exact ne_of_gt (foldPosteriorNormalizer_pos prior visible hprior hvisible_pos)
  have hfactor :
      ∀ θ', foldSampleLikelihood (foldUniformLift F (π θ') d) sample = c * visible θ' := by
    intro θ'
    unfold c visible
    simpa using foldSampleLikelihood_uniformLift_factorization F (π θ') d sample
  calc
    foldPosteriorMass prior
        (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ
        = foldPosteriorMass prior (fun θ' => c * visible θ') θ := by
            simp [foldPosteriorMass, hfactor]
    _ = foldPosteriorMass prior visible θ :=
          foldPosteriorMass_common_factor prior visible c θ hc hnorm
    _ = foldPosteriorMass prior
          (fun θ' => foldVisibleSampleLikelihood F (π θ') sample) θ := by
            rfl

lemma foldPosteriorMass_eq_of_visibleEquivalent {n : ℕ}
    (F : α → β) (d : β → ℝ) (π : Θ → β → ℝ) (prior : Θ → ℝ)
    (sample sample' : Fin n → α)
    (hd : ∀ x, 0 < d x)
    (hπ : ∀ θ x, 0 < π θ x)
    (hprior : ∀ θ, 0 < prior θ)
    (hvis : foldVisibleEquivalent F sample sample') :
    ∀ θ,
      foldPosteriorMass prior
          (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ =
        foldPosteriorMass prior
          (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample') θ := by
  intro θ
  have hcollapse :=
    foldPosteriorMass_eq_visible_of_uniformLift F d π prior sample hd hπ hprior
  have hcollapse' :=
    foldPosteriorMass_eq_visible_of_uniformLift F d π prior sample' hd hπ hprior
  have hvisible :
      ∀ θ', foldVisibleSampleLikelihood F (π θ') sample =
        foldVisibleSampleLikelihood F (π θ') sample' := by
    intro θ'
    exact foldVisibleSampleLikelihood_congr F (π θ') sample sample' hvis
  calc
    foldPosteriorMass prior
        (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ
        = foldPosteriorMass prior
            (fun θ' => foldVisibleSampleLikelihood F (π θ') sample) θ :=
          hcollapse θ
    _ = foldPosteriorMass prior
          (fun θ' => foldVisibleSampleLikelihood F (π θ') sample') θ := by
            simp [foldPosteriorMass, hvisible]
    _ = foldPosteriorMass prior
          (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample') θ := by
            symm
            exact hcollapse' θ

set_option maxHeartbeats 400000 in
/-- Paper label: `thm:op-algebra-fold-bayes-posterior-collapse`.
For fiber-uniform models `μ_θ = Q_m π_θ`, finite-sample likelihoods split into a visible
`π_θ` term times a θ-independent fiber factor, so Bayes posteriors collapse from microscopic
samples to their visible fold images. -/
theorem paper_op_algebra_fold_bayes_posterior_collapse {n : ℕ}
    (F : α → β) (d : β → ℝ) (π : Θ → β → ℝ) (prior : Θ → ℝ)
    (sample : Fin n → α)
    (hd : ∀ x, 0 < d x)
    (hπ : ∀ θ x, 0 < π θ x)
    (hprior : ∀ θ, 0 < prior θ) :
    (∀ θ,
      foldSampleLikelihood (foldUniformLift F (π θ) d) sample =
        foldFiberFactor F d sample * foldVisibleSampleLikelihood F (π θ) sample) ∧
    (∀ θ,
      foldPosteriorMass prior
          (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ =
        foldPosteriorMass prior
          (fun θ' => foldVisibleSampleLikelihood F (π θ') sample) θ) ∧
    (∀ sample' : Fin n → α,
      foldVisibleEquivalent F sample sample' →
        ∀ θ,
          foldPosteriorMass prior
              (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample) θ =
            foldPosteriorMass prior
              (fun θ' => foldSampleLikelihood (foldUniformLift F (π θ') d) sample') θ) := by
  refine ⟨?_, ?_, ?_⟩
  · intro θ
    exact foldSampleLikelihood_uniformLift_factorization F (π θ) d sample
  · exact foldPosteriorMass_eq_visible_of_uniformLift F d π prior sample hd hπ hprior
  · intro sample' hvis θ
    exact foldPosteriorMass_eq_of_visibleEquivalent F d π prior sample sample' hd hπ hprior hvis θ

end

end Omega.OperatorAlgebra
