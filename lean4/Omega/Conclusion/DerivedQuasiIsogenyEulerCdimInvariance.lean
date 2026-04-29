import Omega.Conclusion.DerivedTorsionCamouflageEulerCdim

namespace Omega.Conclusion

/-- Paper label: `cor:conclusion-derived-quasi-isogeny-euler-cdim-invariance`. -/
theorem paper_conclusion_derived_quasi_isogeny_euler_cdim_invariance
    (C D : conclusion_derived_torsion_camouflage_euler_cdim_data)
    (h0 :
      C.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h0FreeRank)
    (h1 :
      C.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h1FreeRank)
    (h2 :
      C.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank =
        D.conclusion_derived_torsion_camouflage_euler_cdim_h2FreeRank) :
    conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim C =
      conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim D := by
  calc
    conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim C =
        conclusion_derived_torsion_camouflage_euler_cdim_eulerRank C := by
          exact (paper_conclusion_derived_torsion_camouflage_euler_cdim C).2.1
    _ = conclusion_derived_torsion_camouflage_euler_cdim_eulerRank D := by
          simp [conclusion_derived_torsion_camouflage_euler_cdim_eulerRank, h0, h1, h2]
    _ = conclusion_derived_torsion_camouflage_euler_cdim_eulerCdim D := by
          exact (paper_conclusion_derived_torsion_camouflage_euler_cdim D).2.1.symm

end Omega.Conclusion
