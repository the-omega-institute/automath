import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Chapter-local seed notion of polynomial equivalence for filtrations. -/
def PolyEquivalent (F F' : ℕ → ℕ) : Prop := ∀ N, F N = F' N

/-- Chapter-local seed for the growth circle dimension attached to a filtration. -/
def gcdimOf (F : ℕ → ℕ) : ℕ := F 0

/-- Polynomially equivalent filtrations have the same seed growth circle dimension.
    thm:gcdim-filtration-invariance -/
theorem paper_gcdim_filtration_invariance (F F' : ℕ → ℕ) (hpoly : PolyEquivalent F F') :
    gcdimOf F = gcdimOf F' := by
  unfold gcdimOf
  simpa [PolyEquivalent] using hpoly 0

end Omega.CircleDimension
