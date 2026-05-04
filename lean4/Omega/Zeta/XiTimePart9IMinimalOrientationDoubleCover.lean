namespace Omega.Zeta

universe u

/-- Paper label: `thm:xi-time-part9i-minimal-orientation-double-cover`. -/
theorem paper_xi_time_part9i_minimal_orientation_double_cover
    (orientationCover pullbackMonodromyAlternating pullbackLocalSystemTrivial : Prop)
    (universalAlternatingFactorization : Type u → Prop)
    (hcover : orientationCover)
    (halt : orientationCover → pullbackMonodromyAlternating)
    (htriv : pullbackMonodromyAlternating → pullbackLocalSystemTrivial)
    (huniv : orientationCover → ∀ Z : Type u, universalAlternatingFactorization Z) :
    pullbackMonodromyAlternating ∧ pullbackLocalSystemTrivial ∧
      ∀ Z : Type u, universalAlternatingFactorization Z := by
  have hAlt : pullbackMonodromyAlternating := halt hcover
  exact ⟨hAlt, htriv hAlt, huniv hcover⟩

end Omega.Zeta
