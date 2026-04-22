import Mathlib.Tactic

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-poisson-cauchy-traceless-quadrupole-factorization`. -/
theorem paper_conclusion_poisson_cauchy_traceless_quadrupole_factorization {A B KL Fisher proj : Real}
    (hKL : KL = A ^ 2 / 8 + B ^ 2 / 2)
    (hFisher : Fisher = A ^ 2 / 2 + 2 * B ^ 2)
    (hProj : proj = A ^ 2 / 16 + B ^ 2 / 4) :
    let hs : Real := A ^ 2 / 2 + 2 * B ^ 2
    KL = hs / 4 /\ Fisher = hs /\ proj = hs / 8 := by
  dsimp
  constructor
  · calc
      KL = A ^ 2 / 8 + B ^ 2 / 2 := hKL
      _ = (A ^ 2 / 2 + 2 * B ^ 2) / 4 := by ring
  constructor
  · exact hFisher
  · calc
      proj = A ^ 2 / 16 + B ^ 2 / 4 := hProj
      _ = (A ^ 2 / 2 + 2 * B ^ 2) / 8 := by ring

end Omega.Conclusion
