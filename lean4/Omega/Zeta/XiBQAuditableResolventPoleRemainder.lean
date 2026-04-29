import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- The local golden-ratio constant used in the audited scalar model. -/
def xi_bq_auditable_resolvent_pole_remainder_phi : ℝ :=
  (1 + Real.sqrt 5) / 2

/-- Finite scalar model for the audited `B_q` resolvent decomposition. The Perron term is kept
separate, while the analytic remainder is encoded by finitely many non-Perron modes with total
mass at most `1`. -/
structure xi_bq_auditable_resolvent_pole_remainder_data where
  q : ℕ
  projector : ℝ
  nonPerronWeight : Fin q → ℝ
  nonPerronEigenvalue : Fin q → ℝ
  q_pos : 1 ≤ q
  nonPerronWeight_nonneg : ∀ k, 0 ≤ nonPerronWeight k
  nonPerronWeight_sum_le_one : ∑ k, nonPerronWeight k ≤ 1
  nonPerronEigenvalue_nonneg : ∀ k, 0 ≤ nonPerronEigenvalue k
  nonPerronEigenvalue_le :
    ∀ k, nonPerronEigenvalue k ≤ xi_bq_auditable_resolvent_pole_remainder_phi ^ (q - 2)
  spectral_gap :
    xi_bq_auditable_resolvent_pole_remainder_phi ^ (q - 2) <
      xi_bq_auditable_resolvent_pole_remainder_phi ^ q

/-- The Perron pole location is the inverse of the leading eigenvalue `φ^q`. -/
def xi_bq_auditable_resolvent_pole_remainder_perronPole
    (D : xi_bq_auditable_resolvent_pole_remainder_data) : ℝ :=
  (xi_bq_auditable_resolvent_pole_remainder_phi ^ D.q)⁻¹

/-- The non-Perron spectral radius bound. -/
def xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius
    (D : xi_bq_auditable_resolvent_pole_remainder_data) : ℝ :=
  xi_bq_auditable_resolvent_pole_remainder_phi ^ (D.q - 2)

/-- The audited analytic remainder: a finite sum over the non-Perron modes. -/
def xi_bq_auditable_resolvent_pole_remainder_remainder
    (D : xi_bq_auditable_resolvent_pole_remainder_data) (z : ℝ) : ℝ :=
  ∑ k, D.nonPerronWeight k / (1 - D.nonPerronEigenvalue k * z)

/-- The scalar resolvent model used in this chapter-local audit. -/
def xi_bq_auditable_resolvent_pole_remainder_resolvent
    (D : xi_bq_auditable_resolvent_pole_remainder_data) (z : ℝ) : ℝ :=
  D.projector / (1 - xi_bq_auditable_resolvent_pole_remainder_phi ^ D.q * z) +
    xi_bq_auditable_resolvent_pole_remainder_remainder D z

/-- The Perron residue with respect to the variable `z`. -/
def xi_bq_auditable_resolvent_pole_remainder_residue
    (D : xi_bq_auditable_resolvent_pole_remainder_data) : ℝ :=
  -D.projector / (xi_bq_auditable_resolvent_pole_remainder_phi ^ D.q)

lemma xi_bq_auditable_resolvent_pole_remainder_phi_pos :
    0 < xi_bq_auditable_resolvent_pole_remainder_phi := by
  unfold xi_bq_auditable_resolvent_pole_remainder_phi
  nlinarith [Real.sqrt_nonneg 5]

lemma xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius_pos
    (D : xi_bq_auditable_resolvent_pole_remainder_data) :
    0 < xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D := by
  unfold xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius
  exact pow_pos xi_bq_auditable_resolvent_pole_remainder_phi_pos _

lemma xi_bq_auditable_resolvent_pole_remainder_perronPole_pos
    (D : xi_bq_auditable_resolvent_pole_remainder_data) :
    0 < xi_bq_auditable_resolvent_pole_remainder_perronPole D := by
  unfold xi_bq_auditable_resolvent_pole_remainder_perronPole
  exact inv_pos.mpr <| pow_pos xi_bq_auditable_resolvent_pole_remainder_phi_pos _

/-- Paper label: `thm:xi-bq-auditable-resolvent-pole-remainder`. In the scalar audited model the
resolvent splits into its Perron pole plus a finite analytic remainder, the remainder is uniformly
bounded by the maximal non-Perron modulus, the Perron pole is the unique nearest singularity, and
its residue is the expected `-φ^{-q} Π_q`. -/
theorem paper_xi_bq_auditable_resolvent_pole_remainder
    (D : xi_bq_auditable_resolvent_pole_remainder_data) {z : ℝ}
    (hz_nonneg : 0 ≤ z)
    (hz :
      z < (xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D)⁻¹) :
    xi_bq_auditable_resolvent_pole_remainder_resolvent D z =
        D.projector / (1 - xi_bq_auditable_resolvent_pole_remainder_phi ^ D.q * z) +
          xi_bq_auditable_resolvent_pole_remainder_remainder D z ∧
      0 < 1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z ∧
      xi_bq_auditable_resolvent_pole_remainder_remainder D z ≤
        (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z)⁻¹ ∧
      xi_bq_auditable_resolvent_pole_remainder_perronPole D <
        (xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D)⁻¹ ∧
      xi_bq_auditable_resolvent_pole_remainder_residue D =
        -(xi_bq_auditable_resolvent_pole_remainder_perronPole D * D.projector) := by
  have hr_pos : 0 < xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D :=
    xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius_pos D
  have hden_pos : 0 < 1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z := by
    have hmul_lt : xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z < 1 := by
      have hz' : z < 1 / xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D := by
        simpa [one_div] using hz
      have hmul_lt' :
          z * xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D < 1 := by
        exact (lt_div_iff₀ hr_pos).mp hz'
      simpa [mul_comm] using hmul_lt'
    linarith
  have hbound_term :
      ∀ k : Fin D.q,
        D.nonPerronWeight k / (1 - D.nonPerronEigenvalue k * z) ≤
          D.nonPerronWeight k / (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := by
    intro k
    have hk_nonneg := D.nonPerronWeight_nonneg k
    have hk_eig_nonneg := D.nonPerronEigenvalue_nonneg k
    have hk_eig_le := D.nonPerronEigenvalue_le k
    have hk_mul_le :
        D.nonPerronEigenvalue k * z ≤
          xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z := by
      exact mul_le_mul_of_nonneg_right hk_eig_le hz_nonneg
    have hk_denom_pos : 0 < 1 - D.nonPerronEigenvalue k * z := by
      linarith
    have hk_denom_le :
        1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z ≤
          1 - D.nonPerronEigenvalue k * z := by
      exact sub_le_sub_left hk_mul_le 1
    exact div_le_div_of_nonneg_left hk_nonneg hden_pos hk_denom_le
  have hsum_bound :
      xi_bq_auditable_resolvent_pole_remainder_remainder D z ≤
        (∑ k, D.nonPerronWeight k) /
          (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := by
    unfold xi_bq_auditable_resolvent_pole_remainder_remainder
    calc
      ∑ k, D.nonPerronWeight k / (1 - D.nonPerronEigenvalue k * z)
        ≤ ∑ k, D.nonPerronWeight k /
            (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := by
              exact Finset.sum_le_sum fun i _ => hbound_term i
      _ = (∑ k, D.nonPerronWeight k) /
            (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := by
            rw [Finset.sum_div]
  have hrema_bound :
      xi_bq_auditable_resolvent_pole_remainder_remainder D z ≤
        (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z)⁻¹ := by
    have hsum_nonneg : 0 ≤ ∑ k, D.nonPerronWeight k := by
      exact Finset.sum_nonneg fun k _ => D.nonPerronWeight_nonneg k
    calc
      xi_bq_auditable_resolvent_pole_remainder_remainder D z
        ≤ (∑ k, D.nonPerronWeight k) /
            (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := hsum_bound
      _ ≤ 1 / (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z) := by
            exact (div_le_div_of_nonneg_right D.nonPerronWeight_sum_le_one hden_pos.le)
      _ = (1 - xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D * z)⁻¹ := by ring
  have hnearest :
      xi_bq_auditable_resolvent_pole_remainder_perronPole D <
        (xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius D)⁻¹ := by
    unfold xi_bq_auditable_resolvent_pole_remainder_perronPole
      xi_bq_auditable_resolvent_pole_remainder_nonPerronRadius
    exact (inv_lt_inv₀ (pow_pos xi_bq_auditable_resolvent_pole_remainder_phi_pos _) hr_pos).2
      D.spectral_gap
  have hresidue :
      xi_bq_auditable_resolvent_pole_remainder_residue D =
        -(xi_bq_auditable_resolvent_pole_remainder_perronPole D * D.projector) := by
    unfold xi_bq_auditable_resolvent_pole_remainder_residue
      xi_bq_auditable_resolvent_pole_remainder_perronPole
    ring
  exact ⟨rfl, hden_pos, hrema_bound, hnearest, hresidue⟩

end

end Omega.Zeta
