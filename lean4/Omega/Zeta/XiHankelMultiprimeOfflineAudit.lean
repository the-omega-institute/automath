import Mathlib

namespace Omega.Zeta

open scoped BigOperators

/-- Concrete multiprime offline-audit data for an integer Hankel certificate. The `j`-th audited
coordinate is the integer linear form `v_j = (Hs)_j`, every audited prime divides every
coordinate in the modular test, and the coordinatewise bound sits below half of the product
modulus. -/
structure xi_hankel_multiprime_offline_audit_Data where
  rows : ℕ
  cols : ℕ
  xi_hankel_multiprime_offline_audit_matrix : Fin rows → Fin cols → ℤ
  xi_hankel_multiprime_offline_audit_vector : Fin cols → ℤ
  xi_hankel_multiprime_offline_audit_audited_primes : List ℕ
  xi_hankel_multiprime_offline_audit_audited_primes_prime :
    ∀ p ∈ xi_hankel_multiprime_offline_audit_audited_primes, Nat.Prime p
  xi_hankel_multiprime_offline_audit_audited_primes_pairwise :
    xi_hankel_multiprime_offline_audit_audited_primes.Pairwise Nat.Coprime
  xi_hankel_multiprime_offline_audit_bound : ℕ
  xi_hankel_multiprime_offline_audit_coordinate_bound :
    ∀ j : Fin rows,
      Int.natAbs
          (∑ i : Fin cols,
            xi_hankel_multiprime_offline_audit_matrix j i *
              xi_hankel_multiprime_offline_audit_vector i) ≤
        xi_hankel_multiprime_offline_audit_bound
  xi_hankel_multiprime_offline_audit_bound_lt_half_product :
    xi_hankel_multiprime_offline_audit_bound <
      xi_hankel_multiprime_offline_audit_audited_primes.prod / 2

namespace xi_hankel_multiprime_offline_audit_Data

/-- The audited product modulus `Q = ∏_{p ∈ P} p`. -/
def xi_hankel_multiprime_offline_audit_product_modulus
    (D : xi_hankel_multiprime_offline_audit_Data) : ℕ :=
  D.xi_hankel_multiprime_offline_audit_audited_primes.prod

/-- The audited integer vector `v = Hs`, written coordinatewise. -/
def xi_hankel_multiprime_offline_audit_coordinate
    (D : xi_hankel_multiprime_offline_audit_Data) (j : Fin D.rows) : ℤ :=
  ∑ i : Fin D.cols,
    D.xi_hankel_multiprime_offline_audit_matrix j i *
      D.xi_hankel_multiprime_offline_audit_vector i

/-- Integral vanishing of the audited vector. -/
def integral_zero_test (D : xi_hankel_multiprime_offline_audit_Data) : Prop :=
  ∀ j : Fin D.rows, D.xi_hankel_multiprime_offline_audit_coordinate j = 0

/-- Modular vanishing at every audited prime. -/
def modular_zero_test (D : xi_hankel_multiprime_offline_audit_Data) : Prop :=
  ∀ p ∈ D.xi_hankel_multiprime_offline_audit_audited_primes,
    ∀ j : Fin D.rows, ((p : ℕ) : ℤ) ∣ D.xi_hankel_multiprime_offline_audit_coordinate j

private lemma xi_hankel_multiprime_offline_audit_list_prod_pos
    {primes : List ℕ} (hprime : ∀ p ∈ primes, Nat.Prime p) : 0 < primes.prod := by
  induction primes with
  | nil =>
      simp
  | cons p ps ih =>
      have hp : 0 < p := (hprime p (by simp)).pos
      have hps : 0 < ps.prod := ih (by
        intro q hq
        exact hprime q (by simp [hq]))
      simp [hp, hps]

private lemma xi_hankel_multiprime_offline_audit_coprime_prod_of_forall
    {p : ℕ} {primes : List ℕ} (hcop : ∀ q ∈ primes, Nat.Coprime p q) :
    Nat.Coprime p primes.prod := by
  induction primes with
  | nil =>
      simp
  | cons q qs ih =>
      have hpq : Nat.Coprime p q := hcop q (by simp)
      have hpqs : Nat.Coprime p qs.prod := ih (by
        intro r hr
        exact hcop r (by simp [hr]))
      simpa using hpq.mul_right hpqs

private lemma xi_hankel_multiprime_offline_audit_prod_dvd_natAbs
    {primes : List ℕ} (hpair : primes.Pairwise Nat.Coprime) {z : ℤ}
    (hdiv : ∀ p ∈ primes, ((p : ℕ) : ℤ) ∣ z) :
    primes.prod ∣ Int.natAbs z := by
  induction primes with
  | nil =>
      simp
  | cons p ps ih =>
      have hhead : ∀ q ∈ ps, Nat.Coprime p q := (List.pairwise_cons.mp hpair).1
      have htail : ps.Pairwise Nat.Coprime := (List.pairwise_cons.mp hpair).2
      have hp_dvd : p ∣ Int.natAbs z := by
        simpa using Int.natAbs_dvd_natAbs.mpr (hdiv p (by simp))
      have hps_dvd : ps.prod ∣ Int.natAbs z := ih htail (by
        intro q hq
        exact hdiv q (by simp [hq]))
      have hcop : Nat.Coprime p ps.prod :=
        xi_hankel_multiprime_offline_audit_coprime_prod_of_forall hhead
      exact Nat.Coprime.mul_dvd_of_dvd_of_dvd hcop hp_dvd hps_dvd

lemma xi_hankel_multiprime_offline_audit_coordinate_natAbs_le_bound
    (D : xi_hankel_multiprime_offline_audit_Data) (j : Fin D.rows) :
    Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) ≤
      D.xi_hankel_multiprime_offline_audit_bound := by
  simpa [xi_hankel_multiprime_offline_audit_coordinate] using
    D.xi_hankel_multiprime_offline_audit_coordinate_bound j

lemma xi_hankel_multiprime_offline_audit_coordinate_eq_zero_of_modular
    (D : xi_hankel_multiprime_offline_audit_Data) (hmod : D.modular_zero_test) (j : Fin D.rows) :
    D.xi_hankel_multiprime_offline_audit_coordinate j = 0 := by
  let Q := D.xi_hankel_multiprime_offline_audit_product_modulus
  have hQ_dvd :
      Q ∣ Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) := by
    exact
      xi_hankel_multiprime_offline_audit_prod_dvd_natAbs
        D.xi_hankel_multiprime_offline_audit_audited_primes_pairwise
        (by
          intro p hp
          exact hmod p hp j)
  have hcoord_le :
      Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) ≤
        D.xi_hankel_multiprime_offline_audit_bound :=
    D.xi_hankel_multiprime_offline_audit_coordinate_natAbs_le_bound j
  have hcoord_lt_half : Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) < Q / 2 :=
    lt_of_le_of_lt hcoord_le D.xi_hankel_multiprime_offline_audit_bound_lt_half_product
  have hQ_pos : 0 < Q := by
    exact
      xi_hankel_multiprime_offline_audit_list_prod_pos
        D.xi_hankel_multiprime_offline_audit_audited_primes_prime
  have hhalf_lt : Q / 2 < Q := by
    omega
  have hcoord_lt : Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) < Q :=
    lt_trans hcoord_lt_half hhalf_lt
  have hzero_abs :
      Int.natAbs (D.xi_hankel_multiprime_offline_audit_coordinate j) = 0 :=
    Nat.eq_zero_of_dvd_of_lt hQ_dvd hcoord_lt
  exact Int.natAbs_eq_zero.mp hzero_abs

end xi_hankel_multiprime_offline_audit_Data

open xi_hankel_multiprime_offline_audit_Data

/-- Paper label: `thm:xi-hankel-multiprime-offline-audit`. If every coordinate of `v = Hs` is
zero modulo each audited prime, then the pairwise-coprime product modulus `Q` also divides every
coordinate; the coordinatewise bound `|v_j| ≤ M < Q / 2` therefore forces `v_j = 0` for every
`j`. The converse implication is immediate. -/
theorem paper_xi_hankel_multiprime_offline_audit (D : xi_hankel_multiprime_offline_audit_Data) :
    D.integral_zero_test <-> D.modular_zero_test := by
  constructor
  · intro hint p hp j
    rw [hint j]
    exact dvd_zero (((p : ℕ) : ℤ))
  · intro hmod j
    exact D.xi_hankel_multiprime_offline_audit_coordinate_eq_zero_of_modular hmod j

end Omega.Zeta
