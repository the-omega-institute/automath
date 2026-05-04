import Mathlib.Analysis.Complex.Norm
import Omega.Zeta.XiDepthHankelDeterminantVandermondeSquare

namespace Omega.Zeta

open scoped BigOperators

/-- The finite diagonal realization attached to a list of atomic scan nodes. -/
def xi_scan_fingerprint_minimal_contraction_realization_diagonal {κ : Nat}
    (nodes : Fin κ → ℂ) (v : Fin κ → ℂ) : Fin κ → ℂ :=
  fun j => nodes j * v j

/-- The cyclic vector used by the finite diagonal realization. -/
def xi_scan_fingerprint_minimal_contraction_realization_cyclic_vector (κ : Nat) :
    Fin κ → ℂ :=
  fun _ => 1

/-- The state functional induced by finite atomic weights. -/
noncomputable def xi_scan_fingerprint_minimal_contraction_realization_state {κ : Nat}
    (weights : Fin κ → ℂ) (v : Fin κ → ℂ) : ℂ :=
  ∑ j : Fin κ, weights j * v j

/-- The finite atomic moment sequence encoded by a diagonal contraction. -/
noncomputable def xi_scan_fingerprint_minimal_contraction_realization_moment {κ : Nat}
    (weights nodes : Fin κ → ℂ) (n : Nat) : ℂ :=
  ∑ j : Fin κ, weights j * nodes j ^ n

/-- Equality of cyclic finite diagonal realizations through all scalar moments. -/
def xi_scan_fingerprint_minimal_contraction_realization_cyclic_moment_equal
    {κ lam : Nat} (weights : Fin κ → ℂ) (nodes : Fin κ → ℂ)
    (weights' : Fin lam → ℂ) (nodes' : Fin lam → ℂ) : Prop :=
  ∀ n : Nat,
    xi_scan_fingerprint_minimal_contraction_realization_moment weights nodes n =
      xi_scan_fingerprint_minimal_contraction_realization_moment weights' nodes' n

lemma xi_scan_fingerprint_minimal_contraction_realization_diagonal_iterate {κ : Nat}
    (nodes : Fin κ → ℂ) (n : Nat) (j : Fin κ) :
    ((xi_scan_fingerprint_minimal_contraction_realization_diagonal nodes)^[n])
        (xi_scan_fingerprint_minimal_contraction_realization_cyclic_vector κ) j =
      nodes j ^ n := by
  induction n with
  | zero =>
      simp [xi_scan_fingerprint_minimal_contraction_realization_cyclic_vector]
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      simp [xi_scan_fingerprint_minimal_contraction_realization_diagonal, ih, pow_succ,
        mul_comm]

lemma xi_scan_fingerprint_minimal_contraction_realization_state_iterate {κ : Nat}
    (D : XiFiniteAtomicMomentData κ) (n : Nat) :
    xi_scan_fingerprint_minimal_contraction_realization_state D.weights
        (((xi_scan_fingerprint_minimal_contraction_realization_diagonal D.nodes)^[n])
          (xi_scan_fingerprint_minimal_contraction_realization_cyclic_vector κ)) =
      D.moments n := by
  rw [D.moments_eq n]
  unfold xi_scan_fingerprint_minimal_contraction_realization_state
  refine Finset.sum_congr rfl ?_
  intro j _
  rw [xi_scan_fingerprint_minimal_contraction_realization_diagonal_iterate]

lemma xi_scan_fingerprint_minimal_contraction_realization_diagonal_contracts {κ : Nat}
    (nodes : Fin κ → ℂ) (hnodes : ∀ j : Fin κ, ‖nodes j‖ ≤ 1)
    (v : Fin κ → ℂ) (j : Fin κ) :
    ‖xi_scan_fingerprint_minimal_contraction_realization_diagonal nodes v j‖ ≤ ‖v j‖ := by
  calc
    ‖xi_scan_fingerprint_minimal_contraction_realization_diagonal nodes v j‖ =
        ‖nodes j‖ * ‖v j‖ := by
          simp [xi_scan_fingerprint_minimal_contraction_realization_diagonal]
    _ ≤ 1 * ‖v j‖ := mul_le_mul_of_nonneg_right (hnodes j) (norm_nonneg (v j))
    _ = ‖v j‖ := one_mul _

/-- Concrete finite-atom realization package: diagonal nodes in the unit disk act by contraction,
the cyclic vector recovers exactly the finite atomic moments, and equality of all cyclic moments is
the uniqueness criterion for finite cyclic diagonal realizations. -/
def xi_scan_fingerprint_minimal_contraction_realization_spec : Prop :=
  ∀ κ : Nat, ∀ D : XiFiniteAtomicMomentData κ,
    (∀ j : Fin κ, ‖D.nodes j‖ ≤ 1) →
      (∀ n : Nat,
        xi_scan_fingerprint_minimal_contraction_realization_state D.weights
            (((xi_scan_fingerprint_minimal_contraction_realization_diagonal D.nodes)^[n])
              (xi_scan_fingerprint_minimal_contraction_realization_cyclic_vector κ)) =
          D.moments n) ∧
      (∀ v : Fin κ → ℂ, ∀ j : Fin κ,
        ‖xi_scan_fingerprint_minimal_contraction_realization_diagonal D.nodes v j‖ ≤ ‖v j‖) ∧
      Fintype.card (Fin κ) = κ ∧
      (∀ lam : Nat, ∀ E : XiFiniteAtomicMomentData lam,
        (∀ n : Nat, D.moments n = E.moments n) →
          xi_scan_fingerprint_minimal_contraction_realization_cyclic_moment_equal
            D.weights D.nodes E.weights E.nodes)

/-- Paper label: `prop:xi-scan-fingerprint-minimal-contraction-realization`. -/
theorem paper_xi_scan_fingerprint_minimal_contraction_realization :
    xi_scan_fingerprint_minimal_contraction_realization_spec := by
  intro κ D hnodes
  refine ⟨?_, ?_, Fintype.card_fin κ, ?_⟩
  · exact xi_scan_fingerprint_minimal_contraction_realization_state_iterate D
  · exact xi_scan_fingerprint_minimal_contraction_realization_diagonal_contracts D.nodes hnodes
  · intro lam E hmoments n
    unfold xi_scan_fingerprint_minimal_contraction_realization_moment
    rw [← D.moments_eq n, ← E.moments_eq n, hmoments n]

end Omega.Zeta
