import Omega.Folding.CircleDimension

namespace Omega.CircleDimension

/-- Paper label: `thm:cdim-nr-nd-semiring-hom-rigidity`. -/
theorem paper_cdim_nr_nd_semiring_hom_rigidity
    (r d : ℕ) (f : (Fin r → ℕ) →+* (Fin d → ℕ)) :
    ∃ σ : Fin d → Fin r, ∀ x : Fin r → ℕ, ∀ j : Fin d, f x j = x (σ j) := by
  simpa using Omega.semiring_hom_rigidity r d f

end Omega.CircleDimension
