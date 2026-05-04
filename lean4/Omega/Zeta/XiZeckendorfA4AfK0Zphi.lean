import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete prefixed stationary AF data for the Zeckendorf `A4` package.  The prefix records the
finite initial segment before the stationary Fibonacci tail. -/
structure xi_zeckendorf_a4_af_k0_zphi_data where
  xi_zeckendorf_a4_af_k0_zphi_prefix : ℤ × ℤ

/-- The rank-two coordinate model for the stationary dimension group. -/
abbrev xi_zeckendorf_a4_af_k0_zphi_lattice : Type :=
  ℤ × ℤ

/-- The explicit order-coordinate map `Ψ(a,b) = a φ + b`. -/
noncomputable def xi_zeckendorf_a4_af_k0_zphi_Psi
    (x : xi_zeckendorf_a4_af_k0_zphi_lattice) : ℝ :=
  (x.1 : ℝ) * Real.goldenRatio + x.2

/-- The Fibonacci refinement matrix, written in the coordinates used by `Ψ`. -/
def xi_zeckendorf_a4_af_k0_zphi_refinement
    (x : xi_zeckendorf_a4_af_k0_zphi_lattice) :
    xi_zeckendorf_a4_af_k0_zphi_lattice :=
  (x.1 + x.2, x.1)

/-- The stationary AF tail has no `K₁` group in this concrete model. -/
def xi_zeckendorf_a4_af_k0_zphi_k1 : Type :=
  Fin 0

namespace xi_zeckendorf_a4_af_k0_zphi_data

/-- Vanishing of the AF `K₁` group. -/
def k1Vanishes (_D : xi_zeckendorf_a4_af_k0_zphi_data) : Prop :=
  IsEmpty xi_zeckendorf_a4_af_k0_zphi_k1

/-- Identification of the ordered rank-two coordinate image with `ℤ[φ]`. -/
noncomputable def k0IdentifiedWithZPhi (_D : xi_zeckendorf_a4_af_k0_zphi_data) : Prop :=
  Set.range xi_zeckendorf_a4_af_k0_zphi_Psi =
    {r : ℝ | ∃ a b : ℤ, r = (a : ℝ) * Real.goldenRatio + b}

/-- The stationary refinement acts as multiplication by `φ` after applying `Ψ`. -/
noncomputable def refinementActsByPhi (_D : xi_zeckendorf_a4_af_k0_zphi_data) : Prop :=
  ∀ x : xi_zeckendorf_a4_af_k0_zphi_lattice,
    xi_zeckendorf_a4_af_k0_zphi_Psi (xi_zeckendorf_a4_af_k0_zphi_refinement x) =
      Real.goldenRatio * xi_zeckendorf_a4_af_k0_zphi_Psi x

end xi_zeckendorf_a4_af_k0_zphi_data

/-- The `Ψ` image is exactly the displayed copy of `ℤ[φ]`. -/
theorem xi_zeckendorf_a4_af_k0_zphi_k0_identified
    (D : xi_zeckendorf_a4_af_k0_zphi_data) : D.k0IdentifiedWithZPhi := by
  ext r
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x.1, x.2, rfl⟩
  · rintro ⟨a, b, rfl⟩
    exact ⟨(a, b), rfl⟩

/-- The coordinate refinement is multiplication by `φ`, using `φ² = φ + 1`. -/
theorem xi_zeckendorf_a4_af_k0_zphi_refinement_compatibility
    (D : xi_zeckendorf_a4_af_k0_zphi_data) : D.refinementActsByPhi := by
  intro x
  rcases x with ⟨a, b⟩
  simp only [xi_zeckendorf_a4_af_k0_zphi_refinement, xi_zeckendorf_a4_af_k0_zphi_Psi,
    Int.cast_add]
  rw [mul_add]
  calc
    ((a : ℝ) + (b : ℝ)) * Real.goldenRatio + (a : ℝ) =
        (a : ℝ) * (Real.goldenRatio + 1) + Real.goldenRatio * (b : ℝ) := by
      ring
    _ = (a : ℝ) * Real.goldenRatio ^ 2 + Real.goldenRatio * (b : ℝ) := by
      rw [Real.goldenRatio_sq]
    _ = Real.goldenRatio * ((a : ℝ) * Real.goldenRatio) +
        Real.goldenRatio * (b : ℝ) := by
      ring

/-- Paper label: `thm:xi-zeckendorf-a4-af-k0-zphi`. -/
theorem paper_xi_zeckendorf_a4_af_k0_zphi (D : xi_zeckendorf_a4_af_k0_zphi_data) :
    D.k1Vanishes ∧ D.k0IdentifiedWithZPhi ∧ D.refinementActsByPhi := by
  exact ⟨⟨Fin.elim0⟩, xi_zeckendorf_a4_af_k0_zphi_k0_identified D,
    xi_zeckendorf_a4_af_k0_zphi_refinement_compatibility D⟩

end Omega.Zeta
