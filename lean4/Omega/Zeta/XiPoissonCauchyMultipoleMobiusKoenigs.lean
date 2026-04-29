import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete affine chart for the Poisson-Cauchy multipole model: the parabolic Möbius action is
translation, the scale map is dilation about `basePoint`, and the Koenigs coordinate is the affine
coordinate centered at that base point. -/
structure xi_poisson_cauchy_multipole_mobius_koenigs_data where
  basePoint : ℝ

namespace xi_poisson_cauchy_multipole_mobius_koenigs_data

/-- Dilation about the distinguished base point. -/
def scaleMap (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) (c x : ℝ) : ℝ :=
  D.basePoint + c * (x - D.basePoint)

/-- The parabolic Möbius action in the affine chart. -/
def mobiusAction (_D : xi_poisson_cauchy_multipole_mobius_koenigs_data) (t x : ℝ) : ℝ :=
  x + t

/-- The Koenigs coordinate linearizing the parabolic action. -/
def koenigsCoordinate (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) (x : ℝ) : ℝ :=
  x - D.basePoint

/-- Scaling conjugates translation by `t` to translation by `λ * t`. -/
def scaleCovariant (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) : Prop :=
  ∀ c t x, D.scaleMap c (D.mobiusAction t x) =
    D.mobiusAction (c * t) (D.scaleMap c x)

/-- The parabolic Möbius maps form an additive semigroup under composition. -/
def mobiusSemigroup (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) : Prop :=
  ∀ s t x, D.mobiusAction s (D.mobiusAction t x) = D.mobiusAction (s + t) x

/-- In Koenigs coordinates, the parabolic action is diagonalized as addition of the parameter. -/
def koenigsDiagonalization (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) : Prop :=
  ∀ t x, D.koenigsCoordinate (D.mobiusAction t x) = D.koenigsCoordinate x + t

end xi_poisson_cauchy_multipole_mobius_koenigs_data

/-- Paper label: `prop:xi-poisson-cauchy-multipole-mobius-koenigs`. -/
theorem paper_xi_poisson_cauchy_multipole_mobius_koenigs
    (D : xi_poisson_cauchy_multipole_mobius_koenigs_data) :
    D.scaleCovariant ∧ D.mobiusSemigroup ∧ D.koenigsDiagonalization := by
  refine ⟨?_, ?_, ?_⟩
  · intro c t x
    simp [xi_poisson_cauchy_multipole_mobius_koenigs_data.scaleMap,
      xi_poisson_cauchy_multipole_mobius_koenigs_data.mobiusAction]
    ring
  · intro s t x
    simp [xi_poisson_cauchy_multipole_mobius_koenigs_data.mobiusAction]
    ring
  · intro t x
    simp [xi_poisson_cauchy_multipole_mobius_koenigs_data.koenigsCoordinate,
      xi_poisson_cauchy_multipole_mobius_koenigs_data.mobiusAction]
    ring

end Omega.Zeta
