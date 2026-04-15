import Mathlib.Tactic

open Finset

namespace Omega.FoldResidualTime.IidBlockFactorization

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

end Omega.FoldResidualTime.IidBlockFactorization
