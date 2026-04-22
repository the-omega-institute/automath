import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.PowModTotient
import Mathlib.Tactic

namespace Omega.Zeta

/-- Tate-uniformized `n`-torsion roots of unity, encoded by their exponent class modulo `n`. -/
abbrev xi_terminal_zm_noncollapsed_boundary_frobenius_period_torsion_root_carrier
    (n : ℕ) := ZMod n

/-- The residual noncollapsed `y`-values are transported along the same Frobenius orbit package. -/
abbrev xi_terminal_zm_noncollapsed_boundary_frobenius_period_residual_y_carrier
    (n : ℕ) := ZMod n

/-- Frobenius on the unramified quadratic residue field acts on the `μ_n`-exponent ledger by
multiplication with `37^2`. -/
def xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar : ℕ := 37 ^ 2

/-- Frobenius on the unramified quadratic residue field acts on the `μ_n`-exponent ledger by
multiplication with `37^2`. -/
def xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map
    (n : ℕ) :
    xi_terminal_zm_noncollapsed_boundary_frobenius_period_torsion_root_carrier n →
      xi_terminal_zm_noncollapsed_boundary_frobenius_period_torsion_root_carrier n :=
  fun u => (xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar : ZMod n) * u

lemma xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map_iterate
    (n k : ℕ)
    (u : xi_terminal_zm_noncollapsed_boundary_frobenius_period_torsion_root_carrier n) :
    ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n)^[k]) u =
      ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar : ZMod n) ^ k) * u := by
  induction k generalizing u with
  | zero =>
      simp
  | succ k ih =>
      simp [Function.iterate_succ_apply', ih,
        xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map, pow_succ,
        mul_left_comm, mul_comm]

/-- Concrete Frobenius-period package for the noncollapsed boundary over the bad prime `37`. -/
def xi_terminal_zm_noncollapsed_boundary_frobenius_period_statement (n : ℕ) : Prop :=
  (2 ≤ n ∧ Nat.Coprime n 37) →
    let f := Nat.totient n
    let q := 37 ^ (2 * f)
    let frob := xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n
    q = 37 ^ (2 * f) ∧
      (∀ u : xi_terminal_zm_noncollapsed_boundary_frobenius_period_torsion_root_carrier n,
        Function.minimalPeriod frob u ∣ f) ∧
      (∀ y : xi_terminal_zm_noncollapsed_boundary_frobenius_period_residual_y_carrier n,
        Function.minimalPeriod frob y ∣ f)

/-- Paper label: `prop:xi-terminal-zm-noncollapsed-boundary-frobenius-period`. -/
theorem paper_xi_terminal_zm_noncollapsed_boundary_frobenius_period (n : ℕ) :
    xi_terminal_zm_noncollapsed_boundary_frobenius_period_statement n := by
  intro hn
  rcases hn with ⟨hn2, hcoprime⟩
  dsimp
  refine ⟨rfl, ?_, ?_⟩
  · intro u
    have hn1 : 1 < n := by omega
    have hcoprime37sq :
        Nat.Coprime xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar n := by
      unfold xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar
      simpa [Nat.coprime_comm] using hcoprime.pow_right 2
    have hpow_one_nat :
        (((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar ^
            Nat.totient n : ℕ) : ZMod n) = 1) := by
      simpa using
        (ZMod.natCast_eq_natCast_iff'
          (xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar ^
            Nat.totient n) 1 n).2
          (by
            simpa [Nat.mod_eq_of_lt hn1] using
              Nat.pow_totient_mod_eq_one hn1 hcoprime37sq)
    have hpow_one :
        ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar : ZMod n) ^
          Nat.totient n) = 1 := by
      simpa using hpow_one_nat
    have hperiodic :
        Function.IsPeriodicPt
          (xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n)
          (Nat.totient n) u := by
      change
        ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n)^[Nat.totient n])
          u = u
      rw [xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map_iterate]
      rw [hpow_one, one_mul]
    exact hperiodic.minimalPeriod_dvd
  · intro y
    have hn1 : 1 < n := by omega
    have hcoprime37sq :
        Nat.Coprime xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar n := by
      unfold xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar
      simpa [Nat.coprime_comm] using hcoprime.pow_right 2
    have hpow_one_nat :
        (((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar ^
            Nat.totient n : ℕ) : ZMod n) = 1) := by
      simpa using
        (ZMod.natCast_eq_natCast_iff'
          (xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar ^
            Nat.totient n) 1 n).2
          (by
            simpa [Nat.mod_eq_of_lt hn1] using
              Nat.pow_totient_mod_eq_one hn1 hcoprime37sq)
    have hpow_one :
        ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_scalar : ZMod n) ^
          Nat.totient n) = 1 := by
      simpa using hpow_one_nat
    have hperiodic :
        Function.IsPeriodicPt
          (xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n)
          (Nat.totient n) y := by
      change
        ((xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map n)^[Nat.totient n])
          y = y
      rw [xi_terminal_zm_noncollapsed_boundary_frobenius_period_frobenius_map_iterate]
      rw [hpow_one, one_mul]
    exact hperiodic.minimalPeriod_dvd

end Omega.Zeta
