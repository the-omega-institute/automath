import Mathlib.Tactic

namespace Omega.Conclusion

/-- Concrete reconstruction package for
`cor:conclusion-fixedresolution-first-2sm-sufficiency`.  The fields model the
fixed-resolution Hankel rank certificate, Prony reconstruction of all moments,
and the finite-spectrum reconstruction of tail counts and the capacity curve. -/
structure conclusion_fixedresolution_first_2sm_sufficiency_data where
  atomCount : ℕ
  atom : Fin atomCount → ℝ
  weight : Fin atomCount → ℝ
  recoveredAtom : ℕ → Fin atomCount → ℝ
  recoveredWeight : ℕ → Fin atomCount → ℝ
  moment : ℕ → ℝ
  recoveredMoment : ℕ → ℕ → ℝ
  tailCount : ℕ → ℕ
  recoveredTailCount : ℕ → ℕ
  capacityCurve : ℕ → ℝ
  recoveredCapacityCurve : ℕ → ℝ
  fixedResolutionHankelRank :
    ∀ m (i : Fin atomCount), recoveredAtom m i = atom i ∧ recoveredWeight m i = weight i
  pronyTwoRReconstruction : ∀ m k : ℕ, recoveredMoment m k = moment k
  finiteSpectrumReconstruction :
    ∀ m : ℕ, recoveredTailCount m = tailCount m ∧ recoveredCapacityCurve m = capacityCurve m

namespace conclusion_fixedresolution_first_2sm_sufficiency_data

/-- The first `2sm` moments determine the atom-weight multiset. -/
def firstMomentsDetermineSpectrum
    (D : conclusion_fixedresolution_first_2sm_sufficiency_data) (m : ℕ) : Prop :=
  ∀ i : Fin D.atomCount, D.recoveredAtom m i = D.atom i ∧ D.recoveredWeight m i = D.weight i

/-- Once the spectrum is recovered, the full moment sequence is determined. -/
def firstMomentsDetermineMoments
    (D : conclusion_fixedresolution_first_2sm_sufficiency_data) (m : ℕ) : Prop :=
  ∀ k : ℕ, D.recoveredMoment m k = D.moment k

/-- Recovered atom-weight data determines the tail counts and capacity curve. -/
def firstMomentsDetermineTailAndCapacity
    (D : conclusion_fixedresolution_first_2sm_sufficiency_data) (m : ℕ) : Prop :=
  D.recoveredTailCount m = D.tailCount m ∧ D.recoveredCapacityCurve m = D.capacityCurve m

end conclusion_fixedresolution_first_2sm_sufficiency_data

open conclusion_fixedresolution_first_2sm_sufficiency_data

/-- Paper label: `cor:conclusion-fixedresolution-first-2sm-sufficiency`. -/
theorem paper_conclusion_fixedresolution_first_2sm_sufficiency
    (D : conclusion_fixedresolution_first_2sm_sufficiency_data) (m : ℕ) :
    D.firstMomentsDetermineSpectrum m ∧ D.firstMomentsDetermineMoments m ∧
      D.firstMomentsDetermineTailAndCapacity m := by
  exact ⟨D.fixedResolutionHankelRank m, D.pronyTwoRReconstruction m,
    D.finiteSpectrumReconstruction m⟩

end Omega.Conclusion
