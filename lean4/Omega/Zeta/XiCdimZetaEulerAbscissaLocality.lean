import Mathlib.Tactic
import Omega.CircleDimension.CircleDim

namespace Omega.Zeta

/-- Arithmetic model for `|G / nG|` when the free rank is `r` and the torsion part is controlled
by the integer `torsion`. -/
def xi_cdim_zeta_euler_abscissa_locality_quotientCard (r torsion n : ℕ) : ℕ :=
  n ^ r * Nat.gcd torsion n

/-- Local prime-power factor in the good-prime regime. -/
def xi_cdim_zeta_euler_abscissa_locality_goodPrimeFactor (r p k : ℕ) : ℕ :=
  (p ^ k) ^ r

/-- Concrete locality package: multiplicativity on coprime moduli, pure free-rank local factors
away from the torsion primes, and the coefficient-growth bounds underlying abscissa `r + 1`. -/
def xi_cdim_zeta_euler_abscissa_locality_statement (r torsion : ℕ) : Prop :=
  Omega.CircleDimension.circleDim r torsion = r ∧
    (∀ m n : ℕ, Nat.Coprime m n →
      xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion (m * n) =
        xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion m *
          xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion n) ∧
    (∀ p k : ℕ, Nat.Prime p → ¬p ∣ torsion →
      xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion (p ^ k) =
        xi_cdim_zeta_euler_abscissa_locality_goodPrimeFactor r p k) ∧
    (∀ n : ℕ, n ^ r ≤ xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion n) ∧
    (∀ n : ℕ,
      xi_cdim_zeta_euler_abscissa_locality_quotientCard r torsion n ≤ torsion * n ^ r)

/-- Paper label: `thm:xi-cdim-zeta-euler-abscissa-locality`. For the standard `ℤ^r ⊕ F` counting
model, the quotient-cardinality function is multiplicative on coprime moduli, all good-prime
local factors coincide with the pure `r`-rank term, and the coefficients are trapped between
`n^r` and `|F| n^r`, which is the finite-locality certificate behind the convergence abscissa
`r + 1`. -/
theorem paper_xi_cdim_zeta_euler_abscissa_locality
    (r torsion : ℕ) (htorsion : 0 < torsion) :
    xi_cdim_zeta_euler_abscissa_locality_statement r torsion := by
  refine ⟨by simp [Omega.CircleDimension.circleDim], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    unfold xi_cdim_zeta_euler_abscissa_locality_quotientCard
    rw [Nat.mul_pow, Nat.Coprime.gcd_mul torsion hmn]
    ac_rfl
  · intro p k hp hbad
    unfold xi_cdim_zeta_euler_abscissa_locality_quotientCard
      xi_cdim_zeta_euler_abscissa_locality_goodPrimeFactor
    rcases k with _ | k
    · simp
    · have hcop : Nat.Coprime torsion (p ^ (k + 1)) := by
        have hcop_tp : Nat.Coprime torsion p := (hp.coprime_iff_not_dvd.2 hbad).symm
        exact (Nat.coprime_pow_right_iff (Nat.succ_pos k) torsion p).2 hcop_tp
      simp [hcop.gcd_eq_one]
  · intro n
    unfold xi_cdim_zeta_euler_abscissa_locality_quotientCard
    have hgcd_pos : 0 < Nat.gcd torsion n := Nat.gcd_pos_of_pos_left n htorsion
    have hone : 1 ≤ Nat.gcd torsion n := Nat.succ_le_of_lt hgcd_pos
    calc
      n ^ r = n ^ r * 1 := by simp
      _ ≤ n ^ r * Nat.gcd torsion n := Nat.mul_le_mul_left _ hone
  · intro n
    unfold xi_cdim_zeta_euler_abscissa_locality_quotientCard
    have hgcd_le : Nat.gcd torsion n ≤ torsion :=
      Nat.le_of_dvd htorsion (Nat.gcd_dvd_left torsion n)
    simpa [Nat.mul_comm, Nat.mul_left_comm, Nat.mul_assoc] using
      Nat.mul_le_mul_left (n ^ r) hgcd_le

end Omega.Zeta
