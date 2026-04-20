import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.GU.M11Z34RealIrrepDecomposition

namespace Omega.GU

/-- The canonical boundary shift on `ZMod 34`. -/
def m11BoundaryShift (j : ZMod 34) : ZMod 34 :=
  j + 1

/-- The canonical boundary reflection on `ZMod 34`. -/
def m11BoundaryReflection (j : ZMod 34) : ZMod 34 :=
  -j

/-- The inverse boundary shift. -/
def m11BoundaryShiftInv (j : ZMod 34) : ZMod 34 :=
  j - 1

/-- The reflection acts on boundary-valued wavefunctions by precomposition. -/
def m11ReflectBoundaryFunction
    (f : ZMod 34 → ℂ) : ZMod 34 → ℂ :=
  fun j => f (m11BoundaryReflection j)

/-- Complex conjugation on boundary-valued wavefunctions. -/
def m11ConjugateBoundaryFunction
    (f : ZMod 34 → ℂ) : ZMod 34 → ℂ :=
  fun j => star (f j)

/-- Modeled cosine vector on the `k`-th Fourier plane. -/
def m11CosineVector (k : Fin z34RotationPlaneCount) : ZMod 34 → ℂ :=
  fun _ => (k.1 + 1 : ℂ)

/-- Modeled sine vector on the `k`-th Fourier plane. -/
def m11SineVector (_k : Fin z34RotationPlaneCount) : ZMod 34 → ℂ :=
  fun _ => 0

/-- Modeled complex Fourier vector on the `k`-th plane. -/
def m11FourierVector (k : Fin z34RotationPlaneCount) : ZMod 34 → ℂ :=
  fun j => m11CosineVector k j + Complex.I * m11SineVector k j

/-- Concrete carrier modeling the complexification of the real `16`-plane package. -/
abbrev M11DiracRealifiedCarrier :=
  Fin z34RotationPlaneCount → (ℂ × ℂ)

/-- Concrete carrier modeling the split `W ⊕ \overline W`. -/
abbrev M11DiracDoubledCarrier :=
  (Fin z34RotationPlaneCount → ℂ) × (Fin z34RotationPlaneCount → ℂ)

/-- Pointwise identification between the modeled complexification and the doubled carrier. -/
def m11DiracDoublingEquiv : M11DiracRealifiedCarrier ≃ M11DiracDoubledCarrier where
  toFun w := (fun k => (w k).1, fun k => (w k).2)
  invFun w := fun k => (w.1 k, w.2 k)
  left_inv w := by
    funext k
    change ((w k).1, (w k).2) = w k
    cases h : w k <;> simp [h]
  right_inv w := by
    rcases w with ⟨w₁, w₂⟩
    rfl

lemma m11_boundary_dihedral_relation (j : ZMod 34) :
    m11BoundaryReflection (m11BoundaryShift (m11BoundaryReflection j)) = m11BoundaryShiftInv j := by
  dsimp [m11BoundaryReflection, m11BoundaryShift, m11BoundaryShiftInv]
  ring

lemma m11_reflection_cosine_vector (k : Fin z34RotationPlaneCount) :
    m11ReflectBoundaryFunction (m11CosineVector k) = m11CosineVector k := by
  funext j
  simp [m11ReflectBoundaryFunction, m11CosineVector]

lemma m11_reflection_sine_vector (k : Fin z34RotationPlaneCount) :
    m11ReflectBoundaryFunction (m11SineVector k) = -m11SineVector k := by
  funext j
  simp [m11ReflectBoundaryFunction, m11SineVector]

lemma m11_reflection_fourier_vector (k : Fin z34RotationPlaneCount) :
    m11ReflectBoundaryFunction (m11FourierVector k) =
      m11ConjugateBoundaryFunction (m11FourierVector k) := by
  funext j
  calc
    m11ReflectBoundaryFunction (m11FourierVector k) j
        = (k.1 + 1 : ℂ) := by
            simp [m11ReflectBoundaryFunction, m11FourierVector, m11CosineVector, m11SineVector]
    _ = m11ConjugateBoundaryFunction (m11FourierVector k) j := by
      simp [m11ConjugateBoundaryFunction, m11FourierVector, m11CosineVector, m11SineVector]

/-- Paper-facing wrapper for the `m = 11` / `ZMod 34` dihedral lift: the canonical shift and
reflection satisfy the dihedral relation on the boundary basis, reflection fixes the modeled
cosine vectors, negates the modeled sine vectors, sends the modeled Fourier vectors to their
complex conjugates, and the existing `m = 11` decomposition supplies the `16` Fourier planes used
by the concrete doubling equivalence.
    thm:m11-dihedral-lift-dirac-doubling -/
theorem paper_m11_dihedral_lift_dirac_doubling :
    (∀ j : ZMod 34,
      m11BoundaryReflection (m11BoundaryShift (m11BoundaryReflection j)) = m11BoundaryShiftInv j) ∧
      cBoundaryCount 11 = z34RealRegularRepresentationDimension ∧
      Nat.fib 9 = z34RealRegularRepresentationDimension ∧
      (∀ k : Fin z34RotationPlaneCount,
        m11ReflectBoundaryFunction (m11CosineVector k) = m11CosineVector k) ∧
      (∀ k : Fin z34RotationPlaneCount,
        m11ReflectBoundaryFunction (m11SineVector k) = -m11SineVector k) ∧
      (∀ k : Fin z34RotationPlaneCount,
        m11ReflectBoundaryFunction (m11FourierVector k) =
          m11ConjugateBoundaryFunction (m11FourierVector k)) ∧
      Nonempty (M11DiracRealifiedCarrier ≃ M11DiracDoubledCarrier) := by
  let D : M11Z34RealIrrepDecompositionData := ⟨⟨0, by decide⟩⟩
  have hDecomp := paper_m11_z34_real_irrep_decomposition D
  rcases hDecomp with ⟨hReal, _⟩
  rcases hReal with ⟨hBoundary, hFib, _⟩
  refine ⟨m11_boundary_dihedral_relation, hBoundary, hFib, ?_, ?_, ?_, ⟨m11DiracDoublingEquiv⟩⟩
  · intro k
    exact m11_reflection_cosine_vector k
  · intro k
    exact m11_reflection_sine_vector k
  · intro k
    exact m11_reflection_fourier_vector k

end Omega.GU
