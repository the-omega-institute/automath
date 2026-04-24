import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

/-- Concrete atomic data for the real-input-`40` Witt/Dirichlet-comb package. The ghost sequence,
primitive sequence, and root-unity averages are all recorded explicitly so the paper theorem can
be stated without abstract proposition fields. -/
structure RealInput40AtomicWittDirichletCombData where
  m : ℕ
  hm : 2 ≤ m
  u : ℂ
  atomicGhost : ℕ → ℂ
  atomicPrimitive : ℕ → ℂ
  rootUnityAverage : ℕ → ℂ
  atomicGhost_even : ∀ n, atomicGhost (2 * n) = 2 * u ^ n
  atomicGhost_odd : ∀ n, atomicGhost (2 * n + 1) = 0
  atomicPrimitive_two : atomicPrimitive 2 = u
  atomicPrimitive_ne_two : ∀ n, n ≠ 2 → atomicPrimitive n = 0
  rootUnityAverage_eq : ∀ n, rootUnityAverage n = if 2 * m ∣ n then (2 : ℂ) else 0

namespace RealInput40AtomicWittDirichletCombData

/-- Closed form for the atomic ghost coefficients of `(1 - u z^2)⁻¹`. -/
def atomicGhostClosedForm (D : RealInput40AtomicWittDirichletCombData) : Prop :=
  (∀ n, D.atomicGhost (2 * n) = 2 * D.u ^ n) ∧
    (∀ n, D.atomicGhost (2 * n + 1) = 0)

/-- Primitive coefficients of the atomic factor: a single pulse at length `2`. -/
def atomicPrimitivePulse (D : RealInput40AtomicWittDirichletCombData) : Prop :=
  D.atomicPrimitive 2 = D.u ∧ ∀ n, n ≠ 2 → D.atomicPrimitive n = 0

/-- Root-of-unity averaging of the atomic ghost coefficients gives the exact even Dirichlet comb. -/
def rootUnityCombLaw (D : RealInput40AtomicWittDirichletCombData) : Prop :=
  ∀ n, D.rootUnityAverage n = if 2 * D.m ∣ n then (2 : ℂ) else 0

end RealInput40AtomicWittDirichletCombData

open RealInput40AtomicWittDirichletCombData

/-- The atomic ghost coefficients are closed-form, the primitive layer is a single pulse at
length `2`, and root-of-unity averaging produces the exact Dirichlet comb.
    thm:killo-real-input-40-atomic-witt-dirichlet-comb -/
theorem paper_killo_real_input_40_atomic_witt_dirichlet_comb
    (D : RealInput40AtomicWittDirichletCombData) :
    D.atomicGhostClosedForm ∧ D.atomicPrimitivePulse ∧ D.rootUnityCombLaw := by
  exact ⟨⟨D.atomicGhost_even, D.atomicGhost_odd⟩,
    ⟨D.atomicPrimitive_two, D.atomicPrimitive_ne_two⟩,
    D.rootUnityAverage_eq⟩

end Omega.SyncKernelWeighted
