import Mathlib.Algebra.Group.Basic
import Omega.POM.BCQuotientUniversal

namespace Omega.POM

/-- Paper label: `cor:pom-anom-supported-on-bc-kernel`. -/
theorem paper_pom_anom_supported_on_bc_kernel
    (D : BCQuotientUniversalData) {A : Type*} [AddGroup A] (chi : D.β → A)
    (hchi : ∃ chiVis : D.BCQuotient → A, ∀ x, chi x = chiVis (D.bcProjection x)) :
    ∀ x y, (D.bcSetoid).r x y → chi x - chi y = 0 := by
  classical
  rcases hchi with ⟨chiVis, hchiVis⟩
  intro x y hxy
  have hproj : D.bcProjection x = D.bcProjection y := Quotient.sound hxy
  calc
    chi x - chi y = chiVis (D.bcProjection x) - chiVis (D.bcProjection y) := by
      rw [hchiVis x, hchiVis y]
    _ = 0 := by simp [hproj]

end Omega.POM
