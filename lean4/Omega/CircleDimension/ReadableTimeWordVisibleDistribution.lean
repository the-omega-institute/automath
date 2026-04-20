import Mathlib.Tactic

namespace Omega.CircleDimension

/-- Readable time words are modeled on the visible four-state quotient used elsewhere in the
chapter. -/
abbrev ReadableTimeWord := Fin 4

/-- The stable visible type space for the readable scan. -/
abbrev ReadableStableTypeSpace := Fin 4

/-- The scan/projection readout records the visible state of the readable word. -/
def readableScanProjectionReadout (w : ReadableTimeWord) : ReadableStableTypeSpace :=
  w

/-- The visible distribution is the Dirac mass at the scanned visible state. -/
def readableVisibleDistribution (w : ReadableTimeWord) : ReadableStableTypeSpace → ℚ :=
  fun v => if v = readableScanProjectionReadout w then 1 else 0

/-- The readout produces a stable visible distribution: unit mass at the scanned state and zero
away from it. -/
def readableHasStableVisibleDistribution (w : ReadableTimeWord) : Prop :=
  readableVisibleDistribution w (readableScanProjectionReadout w) = 1 ∧
    ∀ v, v ≠ readableScanProjectionReadout w → readableVisibleDistribution w v = 0

/-- Every readable time word is sent by the scan/projection readout to a stable visible
distribution.
    prop:cdim-readable-time-word-visible-distribution -/
theorem paper_cdim_readable_time_word_visible_distribution :
    ∀ w : ReadableTimeWord, readableHasStableVisibleDistribution w := by
  intro w
  refine ⟨?_, ?_⟩
  · simp [readableVisibleDistribution, readableScanProjectionReadout]
  · intro v hv
    have hv' : v ≠ w := by
      simpa [readableScanProjectionReadout] using hv
    simp [readableVisibleDistribution, readableScanProjectionReadout, hv']

end Omega.CircleDimension
