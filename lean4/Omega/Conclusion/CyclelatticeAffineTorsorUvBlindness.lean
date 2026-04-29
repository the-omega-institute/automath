import Mathlib

namespace Omega.Conclusion

/-- Paper label: `thm:conclusion-cyclelattice-affine-torsor-uv-blindness`.

The zero dual-lattice term in the Poisson-expanded affine theta interface. -/
noncomputable def conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm : ℝ :=
  1

/-- A single nonzero dual term, bounded by the minimum positive quadratic energy. -/
noncomputable def conclusion_cyclelattice_affine_torsor_uv_blindness_nonzeroTerm
    (t c phase : ℝ) : ℝ :=
  Real.exp (-c / t) * phase

/-- The two-term affine theta interface: zero dual term plus one controlled nonzero tail. -/
noncomputable def conclusion_cyclelattice_affine_torsor_uv_blindness_thetaInterface
    (t c phase : ℝ) : ℝ :=
  conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm +
    conclusion_cyclelattice_affine_torsor_uv_blindness_nonzeroTerm t c phase

/-- Concrete UV-blindness statement: the zero dual-lattice contribution is independent of the
affine phase, and every phase of modulus at most one contributes only the exponential tail
controlled by the positive minimum energy `c`. -/
def conclusion_cyclelattice_affine_torsor_uv_blindness_statement : Prop :=
  ∀ t c phase : ℝ, 0 < t → 0 < c → |phase| ≤ 1 →
    conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm = 1 ∧
      |conclusion_cyclelattice_affine_torsor_uv_blindness_thetaInterface t c phase -
          conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm| ≤ Real.exp (-c / t)

theorem paper_conclusion_cyclelattice_affine_torsor_uv_blindness :
    conclusion_cyclelattice_affine_torsor_uv_blindness_statement := by
  intro t c phase _ht _hc hphase
  refine ⟨rfl, ?_⟩
  have hexp_nonneg : 0 ≤ Real.exp (-c / t) := le_of_lt (Real.exp_pos _)
  calc
    |conclusion_cyclelattice_affine_torsor_uv_blindness_thetaInterface t c phase -
        conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm|
        = |Real.exp (-c / t) * phase| := by
          simp [conclusion_cyclelattice_affine_torsor_uv_blindness_thetaInterface,
            conclusion_cyclelattice_affine_torsor_uv_blindness_zeroTerm,
            conclusion_cyclelattice_affine_torsor_uv_blindness_nonzeroTerm]
    _ = Real.exp (-c / t) * |phase| := by
          rw [abs_mul, abs_of_nonneg hexp_nonneg]
    _ ≤ Real.exp (-c / t) * 1 := by
          exact mul_le_mul_of_nonneg_left hphase hexp_nonneg
    _ = Real.exp (-c / t) := by ring

end Omega.Conclusion
