import Mathlib.Tactic

namespace Omega.Folding

/-- Scalar model for the Poisson-dual main term of a weighted cycle-lattice theta series. -/
def graphCycleThetaKernel (rank : ℕ) (gammaDet dualMass t : ℚ) : ℚ :=
  dualMass / (gammaDet * t ^ rank)

/-- Paper label: `thm:graph-cycle-lattice-theta-modular-inversion`.

For the scalar cycle-lattice model, inversion in `t` rescales by the expected power `t^(2 rank)`,
and the rank-one specialization is the Jacobi-style `1 / t` kernel. -/
theorem paper_graph_cycle_lattice_theta_modular_inversion
    (rank : ℕ) (gammaDet dualMass t : ℚ) (hγ : gammaDet ≠ 0) (ht : t ≠ 0) :
    graphCycleThetaKernel rank gammaDet dualMass t =
      (1 / t ^ (2 * rank)) * graphCycleThetaKernel rank gammaDet dualMass (1 / t) ∧
      graphCycleThetaKernel rank gammaDet dualMass t =
        (dualMass / gammaDet) / t ^ rank ∧
      graphCycleThetaKernel 1 gammaDet dualMass t = dualMass / (gammaDet * t) := by
  have hpow : t ^ rank ≠ 0 := pow_ne_zero rank ht
  have hpow2 : t ^ (2 * rank) ≠ 0 := pow_ne_zero (2 * rank) ht
  have hinvpow : (1 / t) ^ rank ≠ 0 := pow_ne_zero rank (one_div_ne_zero ht)
  constructor
  · unfold graphCycleThetaKernel
    rw [one_div_pow]
    field_simp [hγ, hpow, hpow2, hinvpow]
    ring
  constructor
  · unfold graphCycleThetaKernel
    field_simp [hγ, hpow]
  · unfold graphCycleThetaKernel
    ring

end Omega.Folding
