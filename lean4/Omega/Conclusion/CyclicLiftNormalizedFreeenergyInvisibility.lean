import Omega.Zeta.FiniteRhPhaseLiftArtin

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `thm:conclusion-cyclic-lift-normalized-freeenergy-invisibility`. -/
theorem paper_conclusion_cyclic_lift_normalized_freeenergy_invisibility
    (D : Omega.Zeta.FiniteRhPhaseLiftArtinData)
    (baseFreeEnergy liftFreeEnergy spectralSum : ℝ)
    (hArtinAverage : D.artinDeterminantFactorization → liftFreeEnergy = baseFreeEnergy)
    (hJensen : baseFreeEnergy = spectralSum) (hD : D.artinDeterminantFactorization) :
    liftFreeEnergy = spectralSum := by
  calc
    liftFreeEnergy = baseFreeEnergy := hArtinAverage hD
    _ = spectralSum := hJensen

end
end Omega.Conclusion
