import Mathlib.Data.Fin.Basic

namespace Omega.Zeta

/-- Concrete Smith-factor data for the exterior-power pairing.

The finite index type records cyclic Smith factors, `smithExponent` records their
exponents, and `complement` is the complementary-exponent involution. -/
structure xi_exterior_power_perfect_pairing_data where
  cyclicFactorCount : ℕ
  smithExponent : Fin cyclicFactorCount → ℕ
  complement : Fin cyclicFactorCount → Fin cyclicFactorCount
  complement_involutive : Function.Involutive complement
  complement_preserves_exponent : ∀ i, smithExponent (complement i) = smithExponent i

namespace xi_exterior_power_perfect_pairing_data

/-- The complementary-exponent involution as an equivalence of Smith-factor indices. -/
def complementEquiv (D : xi_exterior_power_perfect_pairing_data) :
    Fin D.cyclicFactorCount ≃ Fin D.cyclicFactorCount where
  toFun := D.complement
  invFun := D.complement
  left_inv := D.complement_involutive
  right_inv := D.complement_involutive

/-- Existence of a nondegenerate blockwise pairing, encoded by an exponent-preserving
Smith-factor equivalence. -/
def exists_nondegenerate_pairing (D : xi_exterior_power_perfect_pairing_data) : Prop :=
  ∃ e : Fin D.cyclicFactorCount ≃ Fin D.cyclicFactorCount,
    ∀ i, D.smithExponent (e i) = D.smithExponent i

/-- Self-duality of the cokernel, encoded by an involutive exponent-preserving
Smith-factor equivalence. -/
def self_dual_cokernel (D : xi_exterior_power_perfect_pairing_data) : Prop :=
  ∃ e : Fin D.cyclicFactorCount ≃ Fin D.cyclicFactorCount,
    Function.Involutive e ∧ ∀ i, D.smithExponent (e i) = D.smithExponent i

end xi_exterior_power_perfect_pairing_data

/-- Paper label: `prop:xi-exterior-power-perfect-pairing`. -/
theorem paper_xi_exterior_power_perfect_pairing (D : xi_exterior_power_perfect_pairing_data) :
    D.exists_nondegenerate_pairing ∧ D.self_dual_cokernel := by
  constructor
  · exact ⟨D.complementEquiv, D.complement_preserves_exponent⟩
  · refine ⟨D.complementEquiv, ?_, D.complement_preserves_exponent⟩
    intro i
    exact D.complement_involutive i

end Omega.Zeta
