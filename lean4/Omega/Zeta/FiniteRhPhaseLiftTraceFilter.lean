import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Tactic
import Omega.Zeta.CyclicDet

namespace Omega.Zeta

open Matrix
open scoped Kronecker

def finite_rh_phase_lift_trace_filter_base : Matrix (Fin 1) (Fin 1) ℤ := 1

/-- Concrete trace-filter package for the `1 × 1` base matrix lifted by the cyclic permutation
channels `P_q`, `q = 2, 3, 4, 5, 6`. Since the base trace is identically `1`, the lifted trace is
exactly the cyclic divisibility filter from the paper. -/
def finite_rh_phase_lift_trace_filter_statement : Prop :=
  (∀ n : ℕ,
      Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ cyclicPerm2) ^ n) =
        if 2 ∣ n then 2 else 0) ∧
    (∀ n : ℕ,
      Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ cyclicPerm3) ^ n) =
        if 3 ∣ n then 3 else 0) ∧
    (∀ n : ℕ,
      Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ cyclicPerm4) ^ n) =
        if 4 ∣ n then 4 else 0) ∧
    (∀ n : ℕ,
      Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ cyclicPerm5) ^ n) =
        if 5 ∣ n then 5 else 0) ∧
    (∀ n : ℕ,
      Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ cyclicPerm6) ^ n) =
        if 6 ∣ n then 6 else 0)

private lemma finite_rh_phase_lift_trace_filter_lift_pow
    {q : ℕ} (P : Matrix (Fin q) (Fin q) ℤ) (n : ℕ) :
    ((finite_rh_phase_lift_trace_filter_base ⊗ₖ P) ^ n) =
      finite_rh_phase_lift_trace_filter_base ⊗ₖ (P ^ n) := by
  induction n with
  | zero =>
      simp [finite_rh_phase_lift_trace_filter_base]
  | succ n ih =>
      calc
        (finite_rh_phase_lift_trace_filter_base ⊗ₖ P) ^ (n + 1)
            = (finite_rh_phase_lift_trace_filter_base ⊗ₖ P) ^ n *
                (finite_rh_phase_lift_trace_filter_base ⊗ₖ P) := by
                  simp [pow_succ]
        _ = (finite_rh_phase_lift_trace_filter_base ⊗ₖ (P ^ n)) *
              (finite_rh_phase_lift_trace_filter_base ⊗ₖ P) := by rw [ih]
        _ = (finite_rh_phase_lift_trace_filter_base * finite_rh_phase_lift_trace_filter_base) ⊗ₖ
              (P ^ n * P) := by
                simpa using (Matrix.mul_kronecker_mul finite_rh_phase_lift_trace_filter_base
                  finite_rh_phase_lift_trace_filter_base (P ^ n) P).symm
        _ = finite_rh_phase_lift_trace_filter_base ⊗ₖ (P ^ (n + 1)) := by
              simp [finite_rh_phase_lift_trace_filter_base, pow_succ]

private lemma finite_rh_phase_lift_trace_filter_lift_trace
    {q : ℕ} (P : Matrix (Fin q) (Fin q) ℤ) (n : ℕ) :
    Matrix.trace ((finite_rh_phase_lift_trace_filter_base ⊗ₖ P) ^ n) = Matrix.trace (P ^ n) := by
  rw [finite_rh_phase_lift_trace_filter_lift_pow]
  rw [Matrix.trace_kronecker]
  simp [finite_rh_phase_lift_trace_filter_base]

private lemma finite_rh_phase_lift_trace_filter_q4
    (n : ℕ) : Matrix.trace (cyclicPerm4 ^ n) = if 4 ∣ n then 4 else 0 := by
  rcases paper_cyclic_lift_trace_filter_q4 with ⟨h0, h1, h2, h3⟩
  by_cases hdiv : 4 ∣ n
  · obtain ⟨k, rfl⟩ := hdiv
    simp [h0]
  · have hmod : n % 4 = 1 ∨ n % 4 = 2 ∨ n % 4 = 3 := by omega
    rcases hmod with hmod | hmod
    · have hn : n = 4 * (n / 4) + 1 := by omega
      have hndiv : ¬4 ∣ 4 * (n / 4) + 1 := by omega
      rw [hn, h1 (n / 4)]
      simp [hndiv]
    · rcases hmod with hmod | hmod
      · have hn : n = 4 * (n / 4) + 2 := by omega
        have hndiv : ¬4 ∣ 4 * (n / 4) + 2 := by omega
        rw [hn, h2 (n / 4)]
        simp [hndiv]
      · have hn : n = 4 * (n / 4) + 3 := by omega
        have hndiv : ¬4 ∣ 4 * (n / 4) + 3 := by omega
        rw [hn, h3 (n / 4)]
        simp [hndiv]

private lemma finite_rh_phase_lift_trace_filter_q5
    (n : ℕ) : Matrix.trace (cyclicPerm5 ^ n) = if 5 ∣ n then 5 else 0 := by
  rcases paper_cyclic_lift_trace_filter_q5 with ⟨h0, h1, h2, h3, h4⟩
  by_cases hdiv : 5 ∣ n
  · obtain ⟨k, rfl⟩ := hdiv
    simp [h0]
  · have hmod : n % 5 = 1 ∨ n % 5 = 2 ∨ n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases hmod with hmod | hmod
    · have hn : n = 5 * (n / 5) + 1 := by omega
      have hndiv : ¬5 ∣ 5 * (n / 5) + 1 := by omega
      rw [hn, pow_add, pow_mul, cyclicPerm5_fifth, one_pow, one_mul, h1]
      simp [hndiv]
    · rcases hmod with hmod | hmod
      · have hn : n = 5 * (n / 5) + 2 := by omega
        have hndiv : ¬5 ∣ 5 * (n / 5) + 2 := by omega
        rw [hn, pow_add, pow_mul, cyclicPerm5_fifth, one_pow, one_mul, h2]
        simp [hndiv]
      · rcases hmod with hmod | hmod
        · have hn : n = 5 * (n / 5) + 3 := by omega
          have hndiv : ¬5 ∣ 5 * (n / 5) + 3 := by omega
          rw [hn, pow_add, pow_mul, cyclicPerm5_fifth, one_pow, one_mul, h3]
          simp [hndiv]
        · have hn : n = 5 * (n / 5) + 4 := by omega
          have hndiv : ¬5 ∣ 5 * (n / 5) + 4 := by omega
          rw [hn, pow_add, pow_mul, cyclicPerm5_fifth, one_pow, one_mul, h4]
          simp [hndiv]

private lemma finite_rh_phase_lift_trace_filter_q6
    (n : ℕ) : Matrix.trace (cyclicPerm6 ^ n) = if 6 ∣ n then 6 else 0 := by
  rcases paper_cyclic_lift_trace_filter_q6 with ⟨h0, h1, h2, h3, h4, h5⟩
  by_cases hdiv : 6 ∣ n
  · obtain ⟨k, rfl⟩ := hdiv
    simp [h0]
  · have hmod :
      n % 6 = 1 ∨ n % 6 = 2 ∨ n % 6 = 3 ∨ n % 6 = 4 ∨ n % 6 = 5 := by omega
    rcases hmod with hmod | hmod
    · have hn : n = 6 * (n / 6) + 1 := by omega
      have hndiv : ¬6 ∣ 6 * (n / 6) + 1 := by omega
      rw [hn, pow_add, pow_mul, cyclicPerm6_sixth, one_pow, one_mul, h1]
      simp [hndiv]
    · rcases hmod with hmod | hmod
      · have hn : n = 6 * (n / 6) + 2 := by omega
        have hndiv : ¬6 ∣ 6 * (n / 6) + 2 := by omega
        rw [hn, pow_add, pow_mul, cyclicPerm6_sixth, one_pow, one_mul, h2]
        simp [hndiv]
      · rcases hmod with hmod | hmod
        · have hn : n = 6 * (n / 6) + 3 := by omega
          have hndiv : ¬6 ∣ 6 * (n / 6) + 3 := by omega
          rw [hn, pow_add, pow_mul, cyclicPerm6_sixth, one_pow, one_mul, h3]
          simp [hndiv]
        · rcases hmod with hmod | hmod
          · have hn : n = 6 * (n / 6) + 4 := by omega
            have hndiv : ¬6 ∣ 6 * (n / 6) + 4 := by omega
            rw [hn, pow_add, pow_mul, cyclicPerm6_sixth, one_pow, one_mul, h4]
            simp [hndiv]
          · have hn : n = 6 * (n / 6) + 5 := by omega
            have hndiv : ¬6 ∣ 6 * (n / 6) + 5 := by omega
            rw [hn, pow_add, pow_mul, cyclicPerm6_sixth, one_pow, one_mul, h5]
            simp [hndiv]

/-- Paper label: `cor:finite-rh-phase-lift-trace-filter`. The `1 × 1` base matrix has trace `1`,
so lifting by `P_q` reduces exactly to the cyclic trace-divisibility filter already formalized for
`q = 2, 3, 4, 5, 6`. -/
theorem paper_finite_rh_phase_lift_trace_filter : finite_rh_phase_lift_trace_filter_statement := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [finite_rh_phase_lift_trace_filter_lift_trace]
    by_cases hdiv : 2 ∣ n
    · obtain ⟨k, rfl⟩ := hdiv
      simp [cyclicPerm2_trace_even]
    · rw [cyclicPerm2_trace_odd n]
      · simp [hdiv]
      · intro hEven
        exact hdiv hEven.two_dvd
  · intro n
    rw [finite_rh_phase_lift_trace_filter_lift_trace]
    by_cases hdiv : 3 ∣ n
    · rw [cyclicPerm3_trace_mod3_zero n hdiv]
      simp [hdiv]
    · rw [cyclicPerm3_trace_mod3_nonzero n hdiv]
      simp [hdiv]
  · intro n
    rw [finite_rh_phase_lift_trace_filter_lift_trace, finite_rh_phase_lift_trace_filter_q4]
  · intro n
    rw [finite_rh_phase_lift_trace_filter_lift_trace, finite_rh_phase_lift_trace_filter_q5]
  · intro n
    rw [finite_rh_phase_lift_trace_filter_lift_trace, finite_rh_phase_lift_trace_filter_q6]

end Omega.Zeta
