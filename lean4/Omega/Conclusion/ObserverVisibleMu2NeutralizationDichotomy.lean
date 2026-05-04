namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-observer-visible-mu2-neutralization-dichotomy`. -/
theorem paper_conclusion_observer_visible_mu2_neutralization_dichotomy
    (originalEquivariantNeutralization minimalDoubleCover explicitSymmetryBreaking : Prop)
    (hNoEquivariant : ¬ originalEquivariantNeutralization)
    (hDichotomy :
      ¬ originalEquivariantNeutralization → minimalDoubleCover ∨ explicitSymmetryBreaking) :
    minimalDoubleCover ∨ explicitSymmetryBreaking := by
  exact hDichotomy hNoEquivariant

end Omega.Conclusion
