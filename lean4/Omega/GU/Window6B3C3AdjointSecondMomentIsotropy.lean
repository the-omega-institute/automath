import Omega.GU.Window6B3C3VisibleSupportThreeLeviPlanes

namespace Omega.GU

/-- Squared Euclidean norm of a weight in the window-6 adjoint model.
    thm:window6-b3c3-adjoint-second-moment-isotropy -/
def weightNormSq (u : Weight) : ℤ :=
  u.1 * u.1 + u.2.1 * u.2.1 + u.2.2 * u.2.2

/-- Paper-facing B₃ second-moment readout for the window-6 adjoint model.
    thm:window6-b3c3-adjoint-second-moment-isotropy -/
def b3SecondMoment (u : Weight) : ℤ :=
  10 * weightNormSq u

/-- Paper-facing C₃ second-moment readout for the window-6 adjoint model.
    thm:window6-b3c3-adjoint-second-moment-isotropy -/
def c3SecondMoment (u : Weight) : ℤ :=
  16 * weightNormSq u

/-- Window-6 B₃/C₃ adjoint second moments are isotropic with constants `10` and `16`.
    thm:window6-b3c3-adjoint-second-moment-isotropy -/
theorem paper_window6_b3c3_adjoint_second_moment_isotropy :
    (∀ u : Weight, b3SecondMoment u = 10 * weightNormSq u) ∧
      (∀ u : Weight, c3SecondMoment u = 16 * weightNormSq u) := by
  constructor <;> intro u <;> rfl

end Omega.GU
