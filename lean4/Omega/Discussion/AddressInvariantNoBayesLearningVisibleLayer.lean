import Mathlib
import Omega.OperatorAlgebra.FoldBayesPosteriorCollapse

namespace Omega.Discussion

open scoped BigOperators
open Omega.OperatorAlgebra

section

variable {Θ X Z : Type*}
variable [Fintype Θ] [DecidableEq Θ] [Nonempty Θ]
variable [Fintype X] [DecidableEq X]
variable [Fintype Z] [DecidableEq Z]

/-- The law of a visible statistic `g(X)` induced from the visible layer law. -/
noncomputable def visibleStatisticLaw
    (visibleLaw : Θ → X → ℝ) (g : X → Z) (θ : Θ) (z : Z) : ℝ :=
  Finset.sum (Finset.univ.filter (fun x => g x = z)) fun x => visibleLaw θ x

lemma visibleStatisticLaw_eq_of_theta_independent
    (visibleLaw : Θ → X → ℝ) (g : X → Z)
    (hvisible : ∀ θ θ' x, visibleLaw θ x = visibleLaw θ' x)
    (θ θ' : Θ) (z : Z) :
    visibleStatisticLaw visibleLaw g θ z = visibleStatisticLaw visibleLaw g θ' z := by
  unfold visibleStatisticLaw
  refine Finset.sum_congr rfl ?_
  intro x hx
  exact hvisible θ θ' x

lemma foldPosteriorMass_eq_prior_of_common_likelihood
    (prior : Θ → ℝ) (hprior_sum : ∑ θ, prior θ = 1)
    (θ : Θ) (c : ℝ) (hc : 0 < c) :
    foldPosteriorMass prior (fun _ : Θ => c) θ = prior θ := by
  have hsum :
      ∑ θ', prior θ' * c = c := by
    calc
      ∑ θ', prior θ' * c = ∑ θ', c * prior θ' := by
        refine Finset.sum_congr rfl ?_
        intro θ' hθ'
        ring
      _ = c * ∑ θ', prior θ' := by
        rw [Finset.mul_sum]
      _ = c := by
        rw [hprior_sum]
        ring
  unfold foldPosteriorMass
  rw [hsum]
  have hc0 : c ≠ 0 := ne_of_gt hc
  calc
    prior θ * c / c = prior θ * (c / c) := by ring
    _ = prior θ * 1 := by rw [div_self hc0]
    _ = prior θ := by ring

/-- Paper-facing visible-layer Bayes impossibility: if the visible law is address-invariant, then
the visible layer has a common `θ`-independent law, any statistic `g(X)` inherits the same common
law, and the Bayes posterior after seeing either `X` or any positive-probability statistic
`g(X)` collapses back to the prior.
    cor:discussion-address-invariant-no-bayes-learning-visible-layer -/
theorem paper_discussion_address_invariant_no_bayes_learning_visible_layer
    (prior : Θ → ℝ) (visibleLaw : Θ → X → ℝ) (g : X → Z)
    (hprior_sum : ∑ θ, prior θ = 1)
    (hvisible : ∀ θ θ' x, visibleLaw θ x = visibleLaw θ' x)
    (hvisible_pos : ∀ θ x, 0 < visibleLaw θ x) :
    (∃ π : X → ℝ, ∀ θ x, visibleLaw θ x = π x) ∧
      (∃ ζ : Z → ℝ, ∀ θ z, visibleStatisticLaw visibleLaw g θ z = ζ z) ∧
      (∀ θ x, foldPosteriorMass prior (fun θ' => visibleLaw θ' x) θ = prior θ) ∧
      (∀ θ z, 0 < visibleStatisticLaw visibleLaw g θ z →
        foldPosteriorMass prior (fun θ' => visibleStatisticLaw visibleLaw g θ' z) θ = prior θ) := by
  obtain ⟨θ0⟩ := ‹Nonempty Θ›
  refine ⟨⟨visibleLaw θ0, ?_⟩, ⟨visibleStatisticLaw visibleLaw g θ0, ?_⟩, ?_, ?_⟩
  · intro θ x
    exact hvisible θ θ0 x
  · intro θ z
    exact visibleStatisticLaw_eq_of_theta_independent visibleLaw g hvisible θ θ0 z
  · intro θ x
    have hfun : (fun θ' => visibleLaw θ' x) = fun _ : Θ => visibleLaw θ x := by
      funext θ'
      exact hvisible θ' θ x
    rw [hfun]
    exact foldPosteriorMass_eq_prior_of_common_likelihood prior hprior_sum θ
      (visibleLaw θ x) (hvisible_pos θ x)
  · intro θ z hz
    have hfun : (fun θ' => visibleStatisticLaw visibleLaw g θ' z) =
        fun _ : Θ => visibleStatisticLaw visibleLaw g θ z := by
      funext θ'
      exact visibleStatisticLaw_eq_of_theta_independent visibleLaw g hvisible θ' θ z
    rw [hfun]
    exact foldPosteriorMass_eq_prior_of_common_likelihood prior hprior_sum θ
      (visibleStatisticLaw visibleLaw g θ z) hz

end

end Omega.Discussion
