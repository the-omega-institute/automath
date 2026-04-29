import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

noncomputable section

/-- Pair index set for the Schur--Poisson mutual-energy ledger. -/
def xi_schur_poisson_mutual_energy_ledger_identity_pair_finset (κ : ℕ) :
    Finset (Fin κ × Fin κ) :=
  (Finset.univ : Finset (Fin κ × Fin κ)).filter fun p => p.1 < p.2

/-- Concrete finite Schur--Poisson ledger system. The Coulomb decomposition and Schur ledger
identity are recorded for the same determinant logarithm, so subtracting them gives the mutual
energy ledger. -/
structure xi_schur_poisson_mutual_energy_ledger_identity_system where
  κ : ℕ
  κ_pos : 0 < κ
  p : Fin κ → ℝ
  pi : Fin κ → ℝ
  rho : Fin κ → Fin κ → ℝ
  detLog : ℝ
  p_pos : ∀ m, 0 < p m
  pi_pos : ∀ m, 0 < pi m
  pi_le_p : ∀ m, pi m ≤ p m
  coulomb_decomposition :
    detLog =
      (∑ m : Fin κ, -Real.log (p m)) +
        2 *
          Finset.sum (xi_schur_poisson_mutual_energy_ledger_identity_pair_finset κ)
            (fun q => -Real.log (rho q.1 q.2))
  schur_ledger : detLog = ∑ m : Fin κ, -Real.log (pi m)

/-- Symmetric two-body mutual energy in the finite point set. -/
def xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy
    (S : xi_schur_poisson_mutual_energy_ledger_identity_system) : ℝ :=
  Finset.sum (xi_schur_poisson_mutual_energy_ledger_identity_pair_finset S.κ)
    (fun q => -Real.log (S.rho q.1 q.2))

/-- The logarithmic Schur ledger entry at step `m`. -/
def xi_schur_poisson_mutual_energy_ledger_identity_entry
    (S : xi_schur_poisson_mutual_energy_ledger_identity_system) (m : Fin S.κ) : ℝ :=
  Real.log (S.p m / S.pi m)

/-- Paper-facing mutual-energy ledger identity with pointwise nonnegativity and average
attainment. -/
def xi_schur_poisson_mutual_energy_ledger_identity_statement
    (S : xi_schur_poisson_mutual_energy_ledger_identity_system) : Prop :=
  2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S =
      ∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m ∧
    (∀ m : Fin S.κ, 0 ≤ xi_schur_poisson_mutual_energy_ledger_identity_entry S m) ∧
      ∃ mstar : Fin S.κ,
        (2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S) / S.κ ≤
          xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar

/-- Paper label: `thm:xi-schur-poisson-mutual-energy-ledger-identity`. -/
theorem paper_xi_schur_poisson_mutual_energy_ledger_identity
    (S : xi_schur_poisson_mutual_energy_ledger_identity_system) :
    xi_schur_poisson_mutual_energy_ledger_identity_statement S := by
  have hledger_identity :
      2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S =
        ∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m := by
    have hsub :
        2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S =
          (∑ m : Fin S.κ, -Real.log (S.pi m)) -
            ∑ m : Fin S.κ, -Real.log (S.p m) := by
      dsimp [xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy] at *
      linarith [S.coulomb_decomposition, S.schur_ledger]
    have hsum :
        (∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m) =
          (∑ m : Fin S.κ, -Real.log (S.pi m)) -
            ∑ m : Fin S.κ, -Real.log (S.p m) := by
      calc
        (∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m) =
            ∑ m : Fin S.κ, (Real.log (S.p m) - Real.log (S.pi m)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          exact Real.log_div (S.p_pos m).ne' (S.pi_pos m).ne'
        _ = (∑ m : Fin S.κ, -Real.log (S.pi m)) -
              ∑ m : Fin S.κ, -Real.log (S.p m) := by
          simp [Finset.sum_sub_distrib]
          ring
    exact hsub.trans hsum.symm
  have hnonneg :
      ∀ m : Fin S.κ, 0 ≤ xi_schur_poisson_mutual_energy_ledger_identity_entry S m := by
    intro m
    have hratio_one : 1 ≤ S.p m / S.pi m := by
      exact (le_div_iff₀ (S.pi_pos m)).2 (by simpa using S.pi_le_p m)
    exact Real.log_nonneg hratio_one
  let m0 : Fin S.κ := ⟨0, S.κ_pos⟩
  have huniv_nonempty : (Finset.univ : Finset (Fin S.κ)).Nonempty := ⟨m0, by simp [m0]⟩
  obtain ⟨mstar, _, hmstar_max⟩ :=
    Finset.exists_max_image (Finset.univ : Finset (Fin S.κ))
      (xi_schur_poisson_mutual_energy_ledger_identity_entry S) huniv_nonempty
  have hsum_le :
      ∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m ≤
        ∑ _ : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar := by
    refine Finset.sum_le_sum ?_
    intro m hm
    exact hmstar_max m (by simp)
  have htotal_le :
      2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S ≤
        (S.κ : ℝ) * xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar := by
    calc
      2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S =
          ∑ m : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S m :=
        hledger_identity
      _ ≤ ∑ _ : Fin S.κ, xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar :=
        hsum_le
      _ = (S.κ : ℝ) * xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar := by
        simp
  have hκ_pos_real : (0 : ℝ) < S.κ := by
    exact_mod_cast S.κ_pos
  have haverage :
      (2 * xi_schur_poisson_mutual_energy_ledger_identity_mutual_energy S) / S.κ ≤
        xi_schur_poisson_mutual_energy_ledger_identity_entry S mstar := by
    apply (div_le_iff₀ hκ_pos_real).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using htotal_le
  exact ⟨hledger_identity, hnonneg, mstar, haverage⟩

end

end Omega.Zeta
