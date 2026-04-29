import Mathlib.Data.Fin.Basic

namespace Omega.Zeta

/-- Concrete finite-coordinate data for the `q >= 2` moment-tower layer.

The three matrix-valued families record the original q-layer operator, its symmetric-power
realization, and the matrix-coordinate realization.  The final hypotheses say that, on every
layer `q >= 2`, the symmetric-power and coordinate models realize the same q-layer operator and
that the original q-layer is invariant under the common conjugacy transport. -/
structure xi_time_part9xf_moment_tower_symmetric_power_closure_data where
  xi_time_part9xf_moment_tower_symmetric_power_closure_rank : ℕ
  xi_time_part9xf_moment_tower_symmetric_power_closure_qLayerOperator :
    ℕ →
      Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank →
        Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank → ℤ
  xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPowerMatrix :
    ℕ →
      Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank →
        Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank → ℤ
  xi_time_part9xf_moment_tower_symmetric_power_closure_coordinateMatrix :
    ℕ →
      Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank →
        Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank → ℤ
  xi_time_part9xf_moment_tower_symmetric_power_closure_commonConjugacy :
    Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank ≃
      Fin xi_time_part9xf_moment_tower_symmetric_power_closure_rank
  xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPower_realizes :
    ∀ q, 2 ≤ q →
      xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPowerMatrix q =
        xi_time_part9xf_moment_tower_symmetric_power_closure_qLayerOperator q
  xi_time_part9xf_moment_tower_symmetric_power_closure_coordinate_realizes :
    ∀ q, 2 ≤ q →
      xi_time_part9xf_moment_tower_symmetric_power_closure_coordinateMatrix q =
        xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPowerMatrix q
  xi_time_part9xf_moment_tower_symmetric_power_closure_qLayer_conjugacy :
    ∀ q, 2 ≤ q → ∀ i j,
      xi_time_part9xf_moment_tower_symmetric_power_closure_qLayerOperator q
          (xi_time_part9xf_moment_tower_symmetric_power_closure_commonConjugacy i)
          (xi_time_part9xf_moment_tower_symmetric_power_closure_commonConjugacy j) =
        xi_time_part9xf_moment_tower_symmetric_power_closure_qLayerOperator q i j

namespace xi_time_part9xf_moment_tower_symmetric_power_closure_data

/-- The coordinate q-layer is closed under the symmetric-power realization for every `q >= 2`. -/
def symmetricPowerClosure
    (D : xi_time_part9xf_moment_tower_symmetric_power_closure_data) : Prop :=
  ∀ q, 2 ≤ q →
    D.xi_time_part9xf_moment_tower_symmetric_power_closure_coordinateMatrix q =
      D.xi_time_part9xf_moment_tower_symmetric_power_closure_qLayerOperator q

/-- The common conjugacy transport preserves all matrix-coordinate q-layers for `q >= 2`. -/
def commonConjugacyInvariant
    (D : xi_time_part9xf_moment_tower_symmetric_power_closure_data) : Prop :=
  ∀ q, 2 ≤ q → ∀ i j,
    D.xi_time_part9xf_moment_tower_symmetric_power_closure_coordinateMatrix q
        (D.xi_time_part9xf_moment_tower_symmetric_power_closure_commonConjugacy i)
        (D.xi_time_part9xf_moment_tower_symmetric_power_closure_commonConjugacy j) =
      D.xi_time_part9xf_moment_tower_symmetric_power_closure_coordinateMatrix q i j

end xi_time_part9xf_moment_tower_symmetric_power_closure_data

/-- Paper label: `thm:xi-time-part9xf-moment-tower-symmetric-power-closure`. -/
theorem paper_xi_time_part9xf_moment_tower_symmetric_power_closure
    (D : xi_time_part9xf_moment_tower_symmetric_power_closure_data) :
    D.symmetricPowerClosure ∧ D.commonConjugacyInvariant := by
  constructor
  · intro q hq
    rw [D.xi_time_part9xf_moment_tower_symmetric_power_closure_coordinate_realizes q hq,
      D.xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPower_realizes q hq]
  · intro q hq i j
    simpa [
      D.xi_time_part9xf_moment_tower_symmetric_power_closure_coordinate_realizes q hq,
      D.xi_time_part9xf_moment_tower_symmetric_power_closure_symmetricPower_realizes q hq]
      using D.xi_time_part9xf_moment_tower_symmetric_power_closure_qLayer_conjugacy q hq i j

end Omega.Zeta
