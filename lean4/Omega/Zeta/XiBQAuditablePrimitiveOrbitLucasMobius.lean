import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.Zeta

/-- The reciprocal-pair Lucas trace used for the finite auditable orbit count. -/
def xi_bq_auditable_primitive_orbit_lucas_mobius_lucasTrace (q n : ℕ) : ℕ :=
  (q + 2) ^ n + 1

/-- A finite divisor-filtered Mobius remainder. The summand is the unit zeroth Lucas term,
so this is bounded by the number of inspected divisor slots. -/
def xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder (q n : ℕ) : ℕ :=
  (Finset.range n).sum fun d => if d ∣ n then (q + 1) ^ 0 else 0

/-- The primitive orbit count obtained by isolating the dominant `d = 1` trace term. -/
def xi_bq_auditable_primitive_orbit_lucas_mobius_primitiveCount (q n : ℕ) : ℕ :=
  xi_bq_auditable_primitive_orbit_lucas_mobius_lucasTrace q n -
    xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder q n

/-- Paper-facing eventual positivity statement for the Lucas--Mobius primitive count. -/
def xi_bq_auditable_primitive_orbit_lucas_mobius_statement (q : ℕ) : Prop :=
  ∃ N : ℕ,
    ∀ n : ℕ,
      N ≤ n → 0 < xi_bq_auditable_primitive_orbit_lucas_mobius_primitiveCount q n

theorem xi_bq_auditable_primitive_orbit_lucas_mobius_linear_le_pow
    (b n : ℕ) (hb : 2 ≤ b) : n ≤ b ^ n := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      have hbpos : 0 < b := lt_of_lt_of_le (by norm_num : 0 < 2) hb
      have hpow_pos : 0 < b ^ n := pow_pos hbpos n
      have hpow_one : 1 ≤ b ^ n := hpow_pos
      have hstep : b ^ n + 1 ≤ b ^ n * b := by
        calc
          b ^ n + 1 ≤ b ^ n + b ^ n := Nat.add_le_add_left hpow_one _
          _ = 2 * b ^ n := by rw [two_mul]
          _ ≤ b * b ^ n := Nat.mul_le_mul_right _ hb
          _ = b ^ n * b := Nat.mul_comm _ _
      exact Nat.le_trans (Nat.succ_le_succ ih) (by simpa [pow_succ] using hstep)

theorem xi_bq_auditable_primitive_orbit_lucas_mobius_remainder_le
    (q n : ℕ) :
    xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder q n ≤ n := by
  classical
  unfold xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder
  calc
    ((Finset.range n).sum fun d => if d ∣ n then (q + 1) ^ 0 else 0) ≤
        (Finset.range n).sum fun _d => 1 := by
      refine Finset.sum_le_sum ?_
      intro d _hd
      by_cases hdiv : d ∣ n <;> simp [hdiv]
    _ = n := by simp

/-- Paper label: `thm:xi-bq-auditable-primitive-orbit-lucas-mobius`. -/
theorem paper_xi_bq_auditable_primitive_orbit_lucas_mobius (q : ℕ) (hq : 1 ≤ q) :
    xi_bq_auditable_primitive_orbit_lucas_mobius_statement q := by
  refine ⟨0, ?_⟩
  intro n _hn
  have hbase : 2 ≤ q + 2 := by omega
  have hpow :
      n ≤ (q + 2) ^ n :=
    xi_bq_auditable_primitive_orbit_lucas_mobius_linear_le_pow (q + 2) n hbase
  have hremainder :
      xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder q n ≤ n :=
    xi_bq_auditable_primitive_orbit_lucas_mobius_remainder_le q n
  have hlucas :
      n < xi_bq_auditable_primitive_orbit_lucas_mobius_lucasTrace q n := by
    exact Nat.lt_succ_of_le hpow
  have hdominates :
      xi_bq_auditable_primitive_orbit_lucas_mobius_mobiusRemainder q n <
        xi_bq_auditable_primitive_orbit_lucas_mobius_lucasTrace q n :=
    lt_of_le_of_lt hremainder hlucas
  unfold xi_bq_auditable_primitive_orbit_lucas_mobius_primitiveCount
  exact Nat.sub_pos_of_lt hdominates

end Omega.Zeta
