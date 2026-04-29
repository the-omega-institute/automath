import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Omega.Conclusion.Window6BoundaryZ6TorsorLocalGlobalMismatch
import Omega.Conclusion.Window6MinimalShellRigidSubcoverRootSlice
import Omega.Conclusion.Window6NoLinearFactorization
import Omega.GU.Window6AbelianizedParityChargeRootCartanSplitting

namespace Omega.Conclusion

abbrev conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate :=
  Omega.GU.Window6BoundaryParityLattice

abbrev conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature :=
  Omega.GU.Window6AbelianizedParityCharge

def conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction {β : Type*}
    (φ : conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature → β) :
    conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate → β :=
  fun boundary => φ (Omega.GU.window6BoundaryCartanInclusion boundary)

lemma conclusion_serrin_window6_minimal_anomaly_certificate_three_bit_lower_bound {r : ℕ}
    (φ : conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature →
      (Fin r → ZMod 2))
    (hinj : Function.Injective
      (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ)) :
    3 ≤ r := by
  have hcard :=
    Fintype.card_le_of_injective
      (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ) hinj
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ 3 ≤ r := by
    omega
  rcases hr with rfl | rfl | rfl | hr
  · exfalso
    norm_num [conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate] at hcard
  · exfalso
    norm_num [conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate] at hcard
  · exfalso
    norm_num [conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate] at hcard
  · exact hr

lemma conclusion_serrin_window6_minimal_anomaly_certificate_three_bit_uniqueness
    (φ : conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature →
      conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate)
    (hinj : Function.Injective
      (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ)) :
    Function.Bijective
      (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ) := by
  refine (Fintype.bijective_iff_injective_and_card
    (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ)).2 ?_
  refine ⟨hinj, ?_⟩
  simp [conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate]

def conclusion_serrin_window6_minimal_anomaly_certificate_statement : Prop :=
  full_fiber_partition_is_not_a_free_finite_group_orbit_partition ∧
    (¬ ∃ k, Omega.GU.TerminalFoldbin6CosetModel k) ∧
    window6BoundaryFiber = ({w100001, w100101, w101001} : Finset (Fin 64)) ∧
    Fintype.card Omega.GU.Window6BoundaryParityBlock = 3 ∧
    Fintype.card conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate =
      2 ^ 3 ∧
    Fintype.card Omega.GU.Window6ParityCoordinate = 21 ∧
    Function.LeftInverse Omega.GU.window6BoundaryCartanProjection
      Omega.GU.window6BoundaryCartanInclusion ∧
    (∀ {r : ℕ}
      (φ : conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature →
        (Fin r → ZMod 2)),
      Function.Injective
          (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ) →
        3 ≤ r) ∧
    (∀ φ : conclusion_serrin_window6_minimal_anomaly_certificate_anomaly_signature →
        conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate,
      Function.Injective
          (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ) →
        Function.Bijective
          (conclusion_serrin_window6_minimal_anomaly_certificate_boundary_restriction φ))

/-- Paper label: `prop:conclusion-serrin-window6-minimal-anomaly-certificate`. The window-`6`
boundary anomaly certificate is exactly the three-word boundary parity block: the full fiber
partition is neither a free finite-group orbit partition nor an affine coset model, the boundary
support is `{100001, 100101, 101001}`, and every quotient of the `21`-coordinate anomaly
signature that remains faithful on boundary parity needs at least `3` binary coordinates, with the
`3`-bit target unique up to bijection. -/
theorem paper_conclusion_serrin_window6_minimal_anomaly_certificate :
    conclusion_serrin_window6_minimal_anomaly_certificate_statement := by
  rcases paper_conclusion_window6_boundary_z6_torsor_local_global_mismatch with ⟨_, hfree⟩
  refine ⟨hfree, paper_conclusion_window6_no_linear_factorization, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [Omega.GU.Window6BoundaryParityBlock]
  · simp [conclusion_serrin_window6_minimal_anomaly_certificate_boundary_certificate]
  · simp [Omega.GU.Window6ParityCoordinate]
  · exact Omega.GU.window6BoundaryCartanProjection_inclusion
  · intro r φ hinj
    exact conclusion_serrin_window6_minimal_anomaly_certificate_three_bit_lower_bound φ hinj
  · intro φ hinj
    exact conclusion_serrin_window6_minimal_anomaly_certificate_three_bit_uniqueness φ hinj

end Omega.Conclusion
