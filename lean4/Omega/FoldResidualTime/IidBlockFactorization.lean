import Mathlib.Tactic

open Finset

namespace Omega.FoldResidualTime.IidBlockFactorization

/-- Paper label: `prop:frt-iid-block-factorization`. The IID block law factors over the finite
coordinate cube as a product of identical one-site sums. -/
def frt_iid_block_factorization_statement : Prop :=
  ∀ {α : Type*} [DecidableEq α] [Fintype α] (ℓ : ℕ) (f : α → ℝ),
    ∑ u : Fin ℓ → α, ∏ j : Fin ℓ, f (u j) = (∑ a : α, f a) ^ ℓ

/-- Paper seed: IID block factorization core identity
    `∑_{u : Fin ℓ → Fin n} ∏_j f (u j) = (∑_a f a) ^ ℓ`.
    This is the Fubini-like independence kernel behind
    `prop:frt-iid-block-factorization`. -/
theorem paper_frt_iid_block_factorization_seeds
    {n ℓ : ℕ} (f : Fin n → ℝ) :
    ∑ u : Fin ℓ → Fin n, ∏ j : Fin ℓ, f (u j) = (∑ a : Fin n, f a) ^ ℓ := by
  simpa using
    (Finset.sum_pow' (s := (Finset.univ : Finset (Fin n))) (f := f) (n := ℓ)).symm

theorem paper_frt_iid_block_factorization_package
    {n ℓ : ℕ} (f : Fin n → ℝ) :
    ∑ u : Fin ℓ → Fin n, ∏ j : Fin ℓ, f (u j) = (∑ a : Fin n, f a) ^ ℓ :=
  paper_frt_iid_block_factorization_seeds f

theorem paper_frt_iid_block_factorization : frt_iid_block_factorization_statement := by
  intro α _ _ ℓ f
  simpa using
    (Finset.sum_pow' (s := (Finset.univ : Finset α)) (f := f) (n := ℓ)).symm

end Omega.FoldResidualTime.IidBlockFactorization
