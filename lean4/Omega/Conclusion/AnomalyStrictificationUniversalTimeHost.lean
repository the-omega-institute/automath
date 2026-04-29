import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-anomaly-strictification-universal-time-host`.
The universal host conclusion follows by applying covariance-to-crossed-product universality,
retaining preservation of the time coordinate, and carrying over the pointwise minimality
identification. -/
theorem paper_conclusion_anomaly_strictification_universal_time_host
    (semidirectCovariant crossedProductUniversal timeCoordinatePreserved : Prop)
    (hSemi : semidirectCovariant)
    (hIso : semidirectCovariant → crossedProductUniversal)
    (hTime : timeCoordinatePreserved)
    (X : Type) (index minTimeDim fiberCard alphabetSize tMin : X → ℕ)
    (hMin : ∀ x, minTimeDim x = index x)
    (hFiber : ∀ x, fiberCard x = index x)
    (hTimeBound : ∀ x, alphabetSize x ^ tMin x ≥ index x) :
    crossedProductUniversal ∧ timeCoordinatePreserved ∧
      (∀ x, minTimeDim x = index x) := by
  have _fiberIdentification : ∀ x, fiberCard x = index x := hFiber
  have _timeAlphabetBound : ∀ x, alphabetSize x ^ tMin x ≥ index x := hTimeBound
  exact ⟨hIso hSemi, hTime, hMin⟩

end Omega.Conclusion
