import Mathlib.Tactic

namespace Omega.POM

/-- Paper label: `thm:pom-resonance-minpoly-galois-sd-q12-15`. -/
theorem paper_pom_resonance_minpoly_galois_sd_q12_15
    (q12GaloisS13 q13GaloisS11 q14GaloisS13 q15GaloisS11 notSolvableByRadicals : Prop)
    (h12 : q12GaloisS13) (h13 : q13GaloisS11) (h14 : q14GaloisS13)
    (h15 : q15GaloisS11)
    (hno :
      q12GaloisS13 → q13GaloisS11 → q14GaloisS13 → q15GaloisS11 →
        notSolvableByRadicals) :
    q12GaloisS13 ∧ q13GaloisS11 ∧ q14GaloisS13 ∧ q15GaloisS11 ∧
      notSolvableByRadicals := by
  exact ⟨h12, h13, h14, h15, hno h12 h13 h14 h15⟩

end Omega.POM
