import Mathlib.Algebra.BigOperators.Ring.List
import Mathlib.Tactic

namespace Omega.Zeta

/-- Explicit root coordinates for the window-`6` `C₃` packet. -/
abbrev XiWindow6Root := ℤ × ℤ × ℤ

def xiRootX : XiWindow6Root → ℤ
  | (x, _, _) => x

def xiRootY : XiWindow6Root → ℤ
  | (_, y, _) => y

def xiRootZ : XiWindow6Root → ℤ
  | (_, _, z) => z

/-- The six long `C₃` roots `± 2 e_i`. -/
def xiWindow6LongRoots : List XiWindow6Root :=
  [((2 : ℤ), 0, 0), ((-2 : ℤ), 0, 0), (0, (2 : ℤ), 0), (0, (-2 : ℤ), 0), (0, 0, (2 : ℤ)),
    (0, 0, (-2 : ℤ))]

/-- The twelve short `C₃` roots `± e_i ± e_j` for `i < j`. -/
def xiWindow6ShortRoots : List XiWindow6Root :=
  [((1 : ℤ), (1 : ℤ), 0), ((1 : ℤ), (-1 : ℤ), 0), (((-1 : ℤ)), (1 : ℤ), 0),
    (((-1 : ℤ)), (-1 : ℤ), 0), ((1 : ℤ), 0, (1 : ℤ)), ((1 : ℤ), 0, (-1 : ℤ)),
    (((-1 : ℤ)), 0, (1 : ℤ)), (((-1 : ℤ)), 0, (-1 : ℤ)), (0, (1 : ℤ), (1 : ℤ)),
    (0, (1 : ℤ), (-1 : ℤ)), (0, (-1 : ℤ), (1 : ℤ)), (0, (-1 : ℤ), (-1 : ℤ))]

/-- The squared linear response of a root against the quadratic probe `(x, y, z)`. -/
def xiRootProbe (x y z : ℤ) (v : XiWindow6Root) : ℤ :=
  x * xiRootX v + y * xiRootY v + z * xiRootZ v

/-- Quadratic response from the six long roots. -/
def xiWindow6LongQuadraticMoment (x y z : ℤ) : ℤ :=
  (xiWindow6LongRoots.map fun v => (xiRootProbe x y z v) ^ 2).sum

/-- Quadratic response from the twelve short roots. -/
def xiWindow6ShortQuadraticMoment (x y z : ℤ) : ℤ :=
  (xiWindow6ShortRoots.map fun v => (xiRootProbe x y z v) ^ 2).sum

/-- Long and short blocks each contribute an isotropic quadratic energy, and together they
recover the full `C₃` equipartition law. -/
def XiWindow6C3QuadraticEnergyEquipartitionStatement : Prop :=
  (∀ x y z : ℤ, xiWindow6LongQuadraticMoment x y z = 8 * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    (∀ x y z : ℤ, xiWindow6ShortQuadraticMoment x y z = 8 * (x ^ 2 + y ^ 2 + z ^ 2)) ∧
    ∀ x y z : ℤ,
      xiWindow6LongQuadraticMoment x y z + xiWindow6ShortQuadraticMoment x y z =
        16 * (x ^ 2 + y ^ 2 + z ^ 2)

private theorem xiWindow6LongQuadraticMoment_closed (x y z : ℤ) :
    xiWindow6LongQuadraticMoment x y z = 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [xiWindow6LongQuadraticMoment, xiWindow6LongRoots, xiRootProbe, xiRootX, xiRootY, xiRootZ]
  ring_nf

private theorem xiWindow6ShortQuadraticMoment_closed (x y z : ℤ) :
    xiWindow6ShortQuadraticMoment x y z = 8 * (x ^ 2 + y ^ 2 + z ^ 2) := by
  simp [xiWindow6ShortQuadraticMoment, xiWindow6ShortRoots, xiRootProbe, xiRootX, xiRootY,
    xiRootZ]
  ring_nf

/-- Paper label: `thm:xi-window6-c3-quadratic-energy-equipartition`. -/
theorem paper_xi_window6_c3_quadratic_energy_equipartition :
    XiWindow6C3QuadraticEnergyEquipartitionStatement := by
  refine ⟨xiWindow6LongQuadraticMoment_closed, xiWindow6ShortQuadraticMoment_closed, ?_⟩
  intro x y z
  rw [xiWindow6LongQuadraticMoment_closed, xiWindow6ShortQuadraticMoment_closed]
  ring_nf

end Omega.Zeta
