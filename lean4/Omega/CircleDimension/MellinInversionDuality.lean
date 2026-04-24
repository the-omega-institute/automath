import Mathlib.Data.Complex.Basic
import Mathlib.Tactic
import Omega.Zeta.MellinUnitarySlice

namespace Omega.CircleDimension

open scoped ComplexConjugate

private lemma unitary_slice_fixed_by_one_minus_conj (t : ℝ) :
    (1 : ℂ) - conj ((1 / 2 : ℂ) + t * Complex.I) = (1 / 2 : ℂ) + t * Complex.I := by
  apply Complex.ext
  · norm_num
  · simp

/-- Paper label: `prop:cdim-mellin-inversion-duality`. -/
theorem paper_cdim_mellin_inversion_duality (f : Omega.Zeta.MellinTestFn) :
    (∀ s : ℂ,
      Omega.Zeta.mellinReadout (Omega.Zeta.mellinDual f) s =
        conj (Omega.Zeta.mellinReadout f (1 - conj s))) ∧
      ∀ t : ℝ,
        Omega.Zeta.mellinReadout (Omega.Zeta.mellinDual f) ((1 / 2 : ℂ) + t * Complex.I) =
          conj (Omega.Zeta.mellinReadout f ((1 / 2 : ℂ) + t * Complex.I)) := by
  refine ⟨Omega.Zeta.paper_xi_mellin_conjugation_identity f, ?_⟩
  intro t
  have hs :
      (1 : ℂ) - (((starRingEnd ℂ) 2)⁻¹ + -(↑t * Complex.I)) = (1 / 2 : ℂ) + t * Complex.I := by
    simpa using unitary_slice_fixed_by_one_minus_conj t
  simpa [hs] using Omega.Zeta.paper_xi_mellin_conjugation_identity f ((1 / 2 : ℂ) + t * Complex.I)

end Omega.CircleDimension
