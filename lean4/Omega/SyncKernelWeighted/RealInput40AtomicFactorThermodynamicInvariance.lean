import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

noncomputable section

/-- Concrete data for the real-input-`40` atomic factor. The pole identity rewrites the
finite-part atomic contribution, while equality of core roots records pressure invariance. -/
structure xi_real_input40_atomic_factor_thermodynamic_invariance_data where
  xi_real_input40_atomic_factor_thermodynamic_invariance_lambda : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_zStar : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_u : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_atomicPrimitive : ℕ → ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_coreFinitePart : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_totalFinitePart : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_coreRoot : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_atomicRoot : ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_pressure : ℝ → ℝ
  xi_real_input40_atomic_factor_thermodynamic_invariance_primitive_two :
    xi_real_input40_atomic_factor_thermodynamic_invariance_atomicPrimitive 2 =
      xi_real_input40_atomic_factor_thermodynamic_invariance_u
  xi_real_input40_atomic_factor_thermodynamic_invariance_primitive_ne_two :
    ∀ n,
      n ≠ 2 →
        xi_real_input40_atomic_factor_thermodynamic_invariance_atomicPrimitive n = 0
  xi_real_input40_atomic_factor_thermodynamic_invariance_zStar_eq :
    xi_real_input40_atomic_factor_thermodynamic_invariance_zStar =
      xi_real_input40_atomic_factor_thermodynamic_invariance_lambda⁻¹
  xi_real_input40_atomic_factor_thermodynamic_invariance_finitePart_eq :
    xi_real_input40_atomic_factor_thermodynamic_invariance_totalFinitePart =
      xi_real_input40_atomic_factor_thermodynamic_invariance_coreFinitePart +
        xi_real_input40_atomic_factor_thermodynamic_invariance_u *
          xi_real_input40_atomic_factor_thermodynamic_invariance_zStar ^ 2
  xi_real_input40_atomic_factor_thermodynamic_invariance_root_eq :
    xi_real_input40_atomic_factor_thermodynamic_invariance_atomicRoot =
      xi_real_input40_atomic_factor_thermodynamic_invariance_coreRoot

namespace xi_real_input40_atomic_factor_thermodynamic_invariance_data

/-- Primitive peeling leaves a single atomic pulse at length `2`. -/
def primitivePeeling
    (D : xi_real_input40_atomic_factor_thermodynamic_invariance_data) : Prop :=
  D.xi_real_input40_atomic_factor_thermodynamic_invariance_atomicPrimitive 2 =
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_u ∧
    ∀ n,
      n ≠ 2 →
        D.xi_real_input40_atomic_factor_thermodynamic_invariance_atomicPrimitive n = 0

/-- The Abel finite part shifts by the atomic term `u / lambda^2`. -/
def finitePartShift
    (D : xi_real_input40_atomic_factor_thermodynamic_invariance_data) : Prop :=
  D.xi_real_input40_atomic_factor_thermodynamic_invariance_totalFinitePart =
    D.xi_real_input40_atomic_factor_thermodynamic_invariance_coreFinitePart +
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_u /
        D.xi_real_input40_atomic_factor_thermodynamic_invariance_lambda ^ 2

/-- The thermodynamic pressure is unchanged because the atomic root is the core root. -/
def pressureInvariant
    (D : xi_real_input40_atomic_factor_thermodynamic_invariance_data) : Prop :=
  D.xi_real_input40_atomic_factor_thermodynamic_invariance_pressure
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_atomicRoot =
    D.xi_real_input40_atomic_factor_thermodynamic_invariance_pressure
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_coreRoot

end xi_real_input40_atomic_factor_thermodynamic_invariance_data

open xi_real_input40_atomic_factor_thermodynamic_invariance_data

/-- Paper label: `thm:xi-real-input40-atomic-factor-thermodynamic-invariance`. -/
theorem paper_xi_real_input40_atomic_factor_thermodynamic_invariance
    (D : xi_real_input40_atomic_factor_thermodynamic_invariance_data) :
    D.primitivePeeling ∧ D.finitePartShift ∧ D.pressureInvariant := by
  refine ⟨⟨D.xi_real_input40_atomic_factor_thermodynamic_invariance_primitive_two,
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_primitive_ne_two⟩, ?_, ?_⟩
  · dsimp [finitePartShift]
    rw [D.xi_real_input40_atomic_factor_thermodynamic_invariance_finitePart_eq,
      D.xi_real_input40_atomic_factor_thermodynamic_invariance_zStar_eq]
    ring
  · dsimp [pressureInvariant]
    rw [D.xi_real_input40_atomic_factor_thermodynamic_invariance_root_eq]

end
end Omega.SyncKernelWeighted
