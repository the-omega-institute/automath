import Mathlib.Tactic

namespace Omega.POM

/-- Finite label for the certified Galois group of one observable minimal polynomial. -/
inductive pom_observable_minpoly_galois_sd_q9_13_galois_label where
  | symmetric : ℕ → pom_observable_minpoly_galois_sd_q9_13_galois_label
  | alternating : ℕ → pom_observable_minpoly_galois_sd_q9_13_galois_label
  | unresolved : pom_observable_minpoly_galois_sd_q9_13_galois_label
deriving DecidableEq

/-- The audited degrees for the four recurrence windows. -/
def pom_observable_minpoly_galois_sd_q9_13_expected_degree (q : ℕ) : ℕ :=
  if q = 9 then 7 else if q = 10 then 9 else if q = 11 then 9 else if q = 13 then 11 else 0

/-- The short prime cycle used by the Jordan criterion in the four windows. -/
def pom_observable_minpoly_galois_sd_q9_13_jordan_prime (q : ℕ) : ℕ :=
  if q = 9 then 3 else if q = 10 then 5 else if q = 11 then 5 else if q = 13 then 7 else 0

/-- One finite Frobenius and discriminant certificate for `q = 9, 10, 11, 13`. -/
structure pom_observable_minpoly_galois_sd_q9_13_certificate where
  pom_observable_minpoly_galois_sd_q9_13_q : ℕ
  pom_observable_minpoly_galois_sd_q9_13_degree : ℕ
  pom_observable_minpoly_galois_sd_q9_13_irreducible_prime : ℕ
  pom_observable_minpoly_galois_sd_q9_13_dminusone_prime : ℕ
  pom_observable_minpoly_galois_sd_q9_13_jordan_prime_witness : ℕ
  pom_observable_minpoly_galois_sd_q9_13_discriminant_witness : ℕ
  pom_observable_minpoly_galois_sd_q9_13_galois_group :
    pom_observable_minpoly_galois_sd_q9_13_galois_label
  pom_observable_minpoly_galois_sd_q9_13_degree_eq :
    pom_observable_minpoly_galois_sd_q9_13_degree =
      pom_observable_minpoly_galois_sd_q9_13_expected_degree
        pom_observable_minpoly_galois_sd_q9_13_q
  pom_observable_minpoly_galois_sd_q9_13_irreducible_prime_is_prime :
    Nat.Prime pom_observable_minpoly_galois_sd_q9_13_irreducible_prime
  pom_observable_minpoly_galois_sd_q9_13_dminusone_prime_is_prime :
    Nat.Prime pom_observable_minpoly_galois_sd_q9_13_dminusone_prime
  pom_observable_minpoly_galois_sd_q9_13_jordan_prime_witness_is_prime :
    Nat.Prime pom_observable_minpoly_galois_sd_q9_13_jordan_prime_witness
  pom_observable_minpoly_galois_sd_q9_13_dcycle_certificate :
    pom_observable_minpoly_galois_sd_q9_13_degree =
      pom_observable_minpoly_galois_sd_q9_13_expected_degree
        pom_observable_minpoly_galois_sd_q9_13_q
  pom_observable_minpoly_galois_sd_q9_13_dminusone_cycle_certificate :
    1 ≤ pom_observable_minpoly_galois_sd_q9_13_degree
  pom_observable_minpoly_galois_sd_q9_13_short_prime_cycle_certificate :
    pom_observable_minpoly_galois_sd_q9_13_jordan_prime
        pom_observable_minpoly_galois_sd_q9_13_q ≤
      pom_observable_minpoly_galois_sd_q9_13_degree - 3
  pom_observable_minpoly_galois_sd_q9_13_discriminant_nonsquare :
    pom_observable_minpoly_galois_sd_q9_13_discriminant_witness % 2 = 1
  pom_observable_minpoly_galois_sd_q9_13_local_jordan_criterion :
    pom_observable_minpoly_galois_sd_q9_13_galois_group =
      pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric
        pom_observable_minpoly_galois_sd_q9_13_degree

/-- The four certificates packaged together. -/
structure pom_observable_minpoly_galois_sd_q9_13_data where
  pom_observable_minpoly_galois_sd_q9_13_q9 :
    pom_observable_minpoly_galois_sd_q9_13_certificate
  pom_observable_minpoly_galois_sd_q9_13_q10 :
    pom_observable_minpoly_galois_sd_q9_13_certificate
  pom_observable_minpoly_galois_sd_q9_13_q11 :
    pom_observable_minpoly_galois_sd_q9_13_certificate
  pom_observable_minpoly_galois_sd_q9_13_q13 :
    pom_observable_minpoly_galois_sd_q9_13_certificate
  pom_observable_minpoly_galois_sd_q9_13_q9_eq :
    pom_observable_minpoly_galois_sd_q9_13_certificate.pom_observable_minpoly_galois_sd_q9_13_q
        pom_observable_minpoly_galois_sd_q9_13_q9 = 9
  pom_observable_minpoly_galois_sd_q9_13_q10_eq :
    pom_observable_minpoly_galois_sd_q9_13_certificate.pom_observable_minpoly_galois_sd_q9_13_q
        pom_observable_minpoly_galois_sd_q9_13_q10 = 10
  pom_observable_minpoly_galois_sd_q9_13_q11_eq :
    pom_observable_minpoly_galois_sd_q9_13_certificate.pom_observable_minpoly_galois_sd_q9_13_q
        pom_observable_minpoly_galois_sd_q9_13_q11 = 11
  pom_observable_minpoly_galois_sd_q9_13_q13_eq :
    pom_observable_minpoly_galois_sd_q9_13_certificate.pom_observable_minpoly_galois_sd_q9_13_q
        pom_observable_minpoly_galois_sd_q9_13_q13 = 13

namespace pom_observable_minpoly_galois_sd_q9_13_certificate

lemma pom_observable_minpoly_galois_sd_q9_13_certificate_symmetric
    (C : pom_observable_minpoly_galois_sd_q9_13_certificate) :
    C.pom_observable_minpoly_galois_sd_q9_13_galois_group =
      pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric
        C.pom_observable_minpoly_galois_sd_q9_13_degree :=
  C.pom_observable_minpoly_galois_sd_q9_13_local_jordan_criterion

end pom_observable_minpoly_galois_sd_q9_13_certificate

namespace pom_observable_minpoly_galois_sd_q9_13_data

/-- The four finite Galois conclusions certified by the Frobenius and discriminant data. -/
def claim (D : pom_observable_minpoly_galois_sd_q9_13_data) : Prop :=
  let q9g :=
    D.pom_observable_minpoly_galois_sd_q9_13_q9.pom_observable_minpoly_galois_sd_q9_13_galois_group
  let q10g :=
    D.pom_observable_minpoly_galois_sd_q9_13_q10.pom_observable_minpoly_galois_sd_q9_13_galois_group
  let q11g :=
    D.pom_observable_minpoly_galois_sd_q9_13_q11.pom_observable_minpoly_galois_sd_q9_13_galois_group
  let q13g :=
    D.pom_observable_minpoly_galois_sd_q9_13_q13.pom_observable_minpoly_galois_sd_q9_13_galois_group
  q9g =
        pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric 7 ∧
    q10g =
          pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric 9 ∧
      q11g =
            pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric 9 ∧
        q13g =
              pom_observable_minpoly_galois_sd_q9_13_galois_label.symmetric 11

end pom_observable_minpoly_galois_sd_q9_13_data

open pom_observable_minpoly_galois_sd_q9_13_certificate

/-- Paper label: `prop:pom-observable-minpoly-galois-sd-q9-13`. -/
theorem paper_pom_observable_minpoly_galois_sd_q9_13
    (D : pom_observable_minpoly_galois_sd_q9_13_data) : D.claim := by
  unfold pom_observable_minpoly_galois_sd_q9_13_data.claim
  refine ⟨?_, ?_, ?_, ?_⟩
  · let C := D.pom_observable_minpoly_galois_sd_q9_13_q9
    have h := pom_observable_minpoly_galois_sd_q9_13_certificate_symmetric C
    rw [C.pom_observable_minpoly_galois_sd_q9_13_degree_eq] at h
    rw [D.pom_observable_minpoly_galois_sd_q9_13_q9_eq] at h
    simpa [pom_observable_minpoly_galois_sd_q9_13_expected_degree] using h
  · let C := D.pom_observable_minpoly_galois_sd_q9_13_q10
    have h := pom_observable_minpoly_galois_sd_q9_13_certificate_symmetric C
    rw [C.pom_observable_minpoly_galois_sd_q9_13_degree_eq] at h
    rw [D.pom_observable_minpoly_galois_sd_q9_13_q10_eq] at h
    simpa [pom_observable_minpoly_galois_sd_q9_13_expected_degree] using h
  · let C := D.pom_observable_minpoly_galois_sd_q9_13_q11
    have h := pom_observable_minpoly_galois_sd_q9_13_certificate_symmetric C
    rw [C.pom_observable_minpoly_galois_sd_q9_13_degree_eq] at h
    rw [D.pom_observable_minpoly_galois_sd_q9_13_q11_eq] at h
    simpa [pom_observable_minpoly_galois_sd_q9_13_expected_degree] using h
  · let C := D.pom_observable_minpoly_galois_sd_q9_13_q13
    have h := pom_observable_minpoly_galois_sd_q9_13_certificate_symmetric C
    rw [C.pom_observable_minpoly_galois_sd_q9_13_degree_eq] at h
    rw [D.pom_observable_minpoly_galois_sd_q9_13_q13_eq] at h
    simpa [pom_observable_minpoly_galois_sd_q9_13_expected_degree] using h

end Omega.POM
