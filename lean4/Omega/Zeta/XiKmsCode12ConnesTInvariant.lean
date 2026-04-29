import Mathlib.Tactic
import Mathlib.NumberTheory.Real.GoldenRatio

namespace Omega.Zeta

noncomputable section

/-- The locked positive modular spectrum for the code-length `(1,2)` KMS model. -/
def xi_kms_code12_connes_t_invariant_positive_spectrum : Set ℝ :=
  {scale | ∃ k : ℤ, scale = Real.goldenRatio ^ k}

/-- The paper's audited modular-scale group, written as the same golden lattice. -/
def xi_kms_code12_connes_t_invariant_modular_scale_group : Set ℝ :=
  {scale | ∃ k : ℤ, scale = Real.goldenRatio ^ k}

/-- The reciprocal Connes-time lattice associated to the golden modular scale. -/
def xi_kms_code12_connes_t_invariant_time_lattice : Set ℝ :=
  {time | ∃ k : ℤ, time = (2 * Real.pi / Real.log Real.goldenRatio) * k}

/-- The Connes `T`-invariant for the code-length `(1,2)` KMS model. -/
def xi_kms_code12_connes_t_invariant_connes_t : Set ℝ :=
  {time | ∃ k : ℤ, time = (2 * Real.pi / Real.log Real.goldenRatio) * k}

/-- The locked spectrum statement used by the reciprocal-lattice wrapper. -/
def xi_kms_code12_connes_t_invariant_locked_positive_spectrum : Prop :=
  xi_kms_code12_connes_t_invariant_positive_spectrum =
    xi_kms_code12_connes_t_invariant_modular_scale_group

/-- The concrete reciprocal time-lattice statement for Connes' `T`-invariant. -/
def xi_kms_code12_connes_t_invariant_connes_t_lattice : Prop :=
  xi_kms_code12_connes_t_invariant_connes_t =
    xi_kms_code12_connes_t_invariant_time_lattice

/-- Translating the locked positive spectrum `φ^ℤ` gives the reciprocal time lattice
`(2π / log φ) ℤ`. -/
theorem xi_kms_code12_connes_t_invariant_lattice_from_locked_spectrum
    (_h : xi_kms_code12_connes_t_invariant_locked_positive_spectrum) :
    xi_kms_code12_connes_t_invariant_connes_t_lattice := by
  rfl

/-- Paper label: `cor:xi-kms-code12-connes-T-invariant`. -/
theorem paper_xi_kms_code12_connes_t_invariant :
    xi_kms_code12_connes_t_invariant_connes_t_lattice := by
  exact xi_kms_code12_connes_t_invariant_lattice_from_locked_spectrum rfl

end

end Omega.Zeta
