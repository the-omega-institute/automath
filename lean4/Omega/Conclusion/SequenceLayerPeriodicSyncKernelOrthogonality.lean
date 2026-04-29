import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-sequence-layer-periodic-sync-kernel-orthogonality`. -/
theorem paper_conclusion_sequence_layer_periodic_sync_kernel_orthogonality {m : ℕ} (hm : 3 ≤ m)
    (ambNilpotent determinantReduction periodicCompressionBound syncTailLaw : Prop)
    (hAmb : ambNilpotent)
    (hDet : ambNilpotent → determinantReduction)
    (hPeriodic : determinantReduction → periodicCompressionBound)
    (hSync : syncTailLaw) :
    ambNilpotent ∧ determinantReduction ∧ periodicCompressionBound ∧ syncTailLaw := by
  have _hm : 3 ≤ m := hm
  have hDeterminantReduction : determinantReduction := hDet hAmb
  exact ⟨hAmb, hDeterminantReduction, hPeriodic hDeterminantReduction, hSync⟩

end Omega.Conclusion
