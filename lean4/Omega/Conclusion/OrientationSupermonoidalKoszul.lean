import Omega.GroupUnification.BdryOrientationFunctorSymmetricMonoidalKoszul

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-orientation-supermonoidal-koszul`. -/
theorem paper_conclusion_orientation_supermonoidal_koszul (m n : Nat) :
    Omega.GroupUnification.orientationKoszulLaw m n := by
  exact Omega.GroupUnification.paper_bdry_orientation_functor_symmetric_monoidal_koszul m n

end Omega.Conclusion
