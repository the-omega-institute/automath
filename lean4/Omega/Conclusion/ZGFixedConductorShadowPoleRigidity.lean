import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Tactic
import Omega.Zeta.XiZGAbelResidueLogDensity

namespace Omega.Conclusion

open scoped BigOperators

/-- The fixed-conductor ZG shadow as a Möbius-weighted divisor sum. -/
def conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow
    (q : ℕ) (D : ℕ → ℝ) : ℝ :=
  ∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d

/-- The divisor-sum factor `σ₁(q)` written as a real-valued finite sum over `Nat.divisors q`. -/
def conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one (q : ℕ) : ℝ :=
  ∑ d ∈ Nat.divisors q, (d : ℝ)

/-- Pole-order model for a simple-pole Laurent term: nonzero residue means order `1`. -/
noncomputable def conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order (residue : ℝ) : ℕ :=
  if residue = 0 then 0 else 1

/-- Every fixed-conductor shadow in this concrete model is either identically zero or carries the
same simple-pole order bookkeeping as the ambient `D_ZG` model. -/
noncomputable def conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow_pole_order (R : ℝ) : ℕ :=
  if R = 0 then 0 else 1

/-- Paper label: `prop:conclusion-zg-fixed-conductor-shadow-pole-rigidity`. The Möbius inversion
formula gives the divisor-sum bound, monotonicity replaces each cylinder mass by `D_ZG`, and the
known positivity of the ZG residue identifies the ambient pole order as simple. -/
theorem paper_conclusion_zg_fixed_conductor_shadow_pole_rigidity
    (q : ℕ) (D : ℕ → ℝ) (DZG : ℝ) (W : Omega.Zeta.XiZGAbelResidueLogDensityWitness)
    (hNonneg : ∀ d ∈ Nat.divisors q, 0 ≤ D d)
    (hMono : ∀ d ∈ Nat.divisors q, D d ≤ DZG)
    (hDZG : 0 ≤ DZG) :
    let R := conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow q D
    |R| ≤ conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q * DZG ∧
      0 ≤ conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q * DZG ∧
      conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow_pole_order R ≤
        conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order W.analytic.residueAtOne ∧
      conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order W.analytic.residueAtOne = 1 := by
  dsimp [conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow]
  have htri :
      |∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d| ≤
        ∑ d ∈ Nat.divisors q,
          |(ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d| := by
    simpa using
      (Finset.abs_sum_le_sum_abs (s := Nat.divisors q)
        (f := fun d => (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d))
  have hmoebius_bound :
      (∑ d ∈ Nat.divisors q,
          |(ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d|) ≤
        ∑ d ∈ Nat.divisors q, (d : ℝ) * D d := by
    refine Finset.sum_le_sum ?_
    intro d hd
    have hmu : |(ArithmeticFunction.moebius (q / d) : ℝ)| ≤ 1 := by
      exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := q / d))
    have hd_nonneg : 0 ≤ (d : ℝ) := by positivity
    have hDd_nonneg : 0 ≤ D d := hNonneg d hd
    calc
      |(ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d|
        = |(ArithmeticFunction.moebius (q / d) : ℝ)| * |(d : ℝ)| * |D d| := by
            rw [abs_mul, abs_mul]
      _ = |(ArithmeticFunction.moebius (q / d) : ℝ)| * ((d : ℝ) * D d) := by
            rw [abs_of_nonneg hd_nonneg, abs_of_nonneg hDd_nonneg]
            ring
      _ ≤ 1 * ((d : ℝ) * D d) := by
            exact mul_le_mul_of_nonneg_right hmu (mul_nonneg hd_nonneg hDd_nonneg)
      _ = (d : ℝ) * D d := by ring
  have hmass_bound :
      (∑ d ∈ Nat.divisors q, (d : ℝ) * D d) ≤
        ∑ d ∈ Nat.divisors q, (d : ℝ) * DZG := by
    refine Finset.sum_le_sum ?_
    intro d hd
    exact mul_le_mul_of_nonneg_left (hMono d hd) (by positivity)
  have hsigma :
      conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q * DZG =
        ∑ d ∈ Nat.divisors q, (d : ℝ) * DZG := by
    unfold conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one
    rw [Finset.sum_mul]
  have hsigma_nonneg :
      0 ≤ conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q := by
    unfold conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one
    positivity
  have hbound :
      |∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d| ≤
        conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q * DZG := by
    calc
      |∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d|
        ≤ ∑ d ∈ Nat.divisors q,
            |(ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d| := htri
      _ ≤ ∑ d ∈ Nat.divisors q, (d : ℝ) * D d := hmoebius_bound
      _ ≤ ∑ d ∈ Nat.divisors q, (d : ℝ) * DZG := hmass_bound
      _ = conclusion_zg_fixed_conductor_shadow_pole_rigidity_sigma_one q * DZG := hsigma.symm
  have hambient_residue_pos : 0 < W.analytic.residueAtOne := by
    rcases Omega.Zeta.paper_xi_zg_abel_residue_log_density W with ⟨_, _, hcritical⟩
    rcases hcritical with ⟨hresidue, hdensity_pos, _⟩
    simpa [hresidue] using hdensity_pos
  have hambient_order :
      conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order W.analytic.residueAtOne = 1 := by
    unfold conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order
    have hne : W.analytic.residueAtOne ≠ 0 := by linarith
    simp [hne]
  have hshadow_order :
      conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow_pole_order
          (∑ d ∈ Nat.divisors q, (ArithmeticFunction.moebius (q / d) : ℝ) * (d : ℝ) * D d) ≤
        conclusion_zg_fixed_conductor_shadow_pole_rigidity_pole_order W.analytic.residueAtOne := by
    rw [hambient_order]
    unfold conclusion_zg_fixed_conductor_shadow_pole_rigidity_shadow_pole_order
    split_ifs <;> omega
  refine ⟨hbound, ?_, hshadow_order, hambient_order⟩
  exact mul_nonneg hsigma_nonneg hDZG

end Omega.Conclusion
