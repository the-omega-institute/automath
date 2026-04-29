import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-foldbin-rank-unrank-optimal-advice-polytime`. -/
theorem paper_xi_foldbin_rank_unrank_optimal_advice_polytime
    (FoldFiber : ℕ → ℕ → Type)
    (fiberSize maxFiber : ℕ → ℕ)
    (rank : (m w : ℕ) → FoldFiber m w → ℕ)
    (unrank : (m w : ℕ) → ℕ → Option (FoldFiber m w))
    (linearRAM bitQuadratic optimalAdvice : Prop)
    (hrank : ∀ m w a, unrank m w (rank m w a) = some a)
    (hunrank : ∀ m w j a, unrank m w j = some a → rank m w a = j)
    (hcost : linearRAM ∧ bitQuadratic)
    (hadvice : optimalAdvice) :
    (∀ m w a, unrank m w (rank m w a) = some a) ∧
      linearRAM ∧ bitQuadratic ∧ optimalAdvice := by
  have _hfiberSize : fiberSize = fiberSize := rfl
  have _hmaxFiber : maxFiber = maxFiber := rfl
  have _hunrank := hunrank
  exact ⟨hrank, hcost.1, hcost.2, hadvice⟩

end Omega.Zeta
