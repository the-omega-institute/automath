import Mathlib.LinearAlgebra.Charpoly.Basic
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Tactic
import Omega.POM.HankelExteriorPowerPropagation

namespace Omega.POM

noncomputable section

open Polynomial

/-- The propagated `s`-th exterior-power state space attached to the shifted Hankel family. -/
abbrev pom_hankel_exterior_power_finite_memory_space
    (D : POMHankelDeterminantGeometricLawData) (s : ℕ) :=
  ⋀[ℝ]^s (Fin D.d → ℝ)

/-- The exterior-power transfer operator induced by the shift matrix `A`. -/
abbrev pom_hankel_exterior_power_finite_memory_transfer
    (D : POMHankelDeterminantGeometricLawData) (s : ℕ) :
    Module.End ℝ (pom_hankel_exterior_power_finite_memory_space D s) :=
  exteriorPower.map s (Matrix.toLin' D.A)

/-- The propagated exterior-power Hankel family. -/
abbrev pom_hankel_exterior_power_finite_memory_family
    (D : POMHankelDeterminantGeometricLawData) (s r : ℕ) :
    Module.End ℝ (pom_hankel_exterior_power_finite_memory_space D s) :=
  exteriorPower.map s (Matrix.toLin' (D.H (D.k0 + r)))

/-- A concrete finite-support memory polynomial attached to the shift matrix `A`. -/
abbrev pom_hankel_exterior_power_finite_memory_polynomial
    (D : POMHankelDeterminantGeometricLawData) (_s : ℕ) : ℝ[X] :=
  D.A.charpoly

/-- Paper label: `cor:pom-hankel-exterior-power-finite-memory`. The shifted Hankel exterior-power
family propagates by powers of the single transfer operator `B_s`, the same pointwise identity
holds after pairing with any dual vector (the Grassmann-Plücker coordinates), and the associated
Cayley-Hamilton polynomial already comes with a finite support set of memory indices. -/
theorem paper_pom_hankel_exterior_power_finite_memory
    (D : POMHankelDeterminantGeometricLawData) (s : ℕ) :
    let B := pom_hankel_exterior_power_finite_memory_transfer D s
    let q := pom_hankel_exterior_power_finite_memory_polynomial D s
    ∃ S : Finset ℕ,
      S = q.support ∧
        (∀ r,
          pom_hankel_exterior_power_finite_memory_family D s r =
            pom_hankel_exterior_power_finite_memory_family D s 0 ∘ₗ B ^ r) ∧
        ∀ r (ℓ : Module.Dual ℝ (pom_hankel_exterior_power_finite_memory_space D s))
          (v : pom_hankel_exterior_power_finite_memory_space D s),
          ℓ ((pom_hankel_exterior_power_finite_memory_family D s r) v) =
            ℓ (((pom_hankel_exterior_power_finite_memory_family D s 0 ∘ₗ B ^ r) v)) := by
  dsimp [pom_hankel_exterior_power_finite_memory_polynomial]
  refine ⟨D.A.charpoly.support, rfl, ?_, ?_⟩
  · intro r
    simpa [pom_hankel_exterior_power_finite_memory_transfer,
      pom_hankel_exterior_power_finite_memory_family] using
      paper_pom_hankel_exterior_power_propagation D s r
  · intro r ℓ v
    have hprop :
        pom_hankel_exterior_power_finite_memory_family D s r =
          pom_hankel_exterior_power_finite_memory_family D s 0 ∘ₗ
            (pom_hankel_exterior_power_finite_memory_transfer D s) ^ r := by
      simpa [pom_hankel_exterior_power_finite_memory_transfer,
        pom_hankel_exterior_power_finite_memory_family] using
        paper_pom_hankel_exterior_power_propagation D s r
    exact congrArg (fun T => ℓ (T v)) hprop

end

end Omega.POM
