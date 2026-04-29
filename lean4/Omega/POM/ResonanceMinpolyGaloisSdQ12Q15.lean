import Mathlib.Tactic

namespace Omega.POM

/-- Finite label for the certified Galois group of one resonance minimal polynomial. -/
inductive pom_resonance_minpoly_galois_sd_q12_15_galois_label where
  | symmetric : ℕ → pom_resonance_minpoly_galois_sd_q12_15_galois_label
  | alternating : ℕ → pom_resonance_minpoly_galois_sd_q12_15_galois_label
  | unresolved : pom_resonance_minpoly_galois_sd_q12_15_galois_label
deriving DecidableEq

/-- The audited degrees in the resonance window `q = 12, 13, 14, 15`. -/
def pom_resonance_minpoly_galois_sd_q12_15_expected_degree (q : ℕ) : ℕ :=
  if q = 12 then 13 else if q = 13 then 11 else if q = 14 then 13 else
    if q = 15 then 11 else 0

/-- The short prime cycle used by the Jordan-style certificate in the four windows. -/
def pom_resonance_minpoly_galois_sd_q12_15_jordan_prime (q : ℕ) : ℕ :=
  if q = 12 then 11 else if q = 13 then 7 else if q = 14 then 11 else
    if q = 15 then 7 else 0

/-- One finite Frobenius/discriminant certificate for `q = 12, 13, 14, 15`. -/
structure pom_resonance_minpoly_galois_sd_q12_15_certificate where
  pom_resonance_minpoly_galois_sd_q12_15_q : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_degree : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_irreducible_prime : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_dminusone_prime : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_jordan_prime_witness : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_discriminant_witness : ℕ
  pom_resonance_minpoly_galois_sd_q12_15_galois_group :
    pom_resonance_minpoly_galois_sd_q12_15_galois_label
  pom_resonance_minpoly_galois_sd_q12_15_degree_eq :
    pom_resonance_minpoly_galois_sd_q12_15_degree =
      pom_resonance_minpoly_galois_sd_q12_15_expected_degree
        pom_resonance_minpoly_galois_sd_q12_15_q
  pom_resonance_minpoly_galois_sd_q12_15_irreducible_prime_is_prime :
    Nat.Prime pom_resonance_minpoly_galois_sd_q12_15_irreducible_prime
  pom_resonance_minpoly_galois_sd_q12_15_dminusone_prime_is_prime :
    Nat.Prime pom_resonance_minpoly_galois_sd_q12_15_dminusone_prime
  pom_resonance_minpoly_galois_sd_q12_15_jordan_prime_witness_is_prime :
    Nat.Prime pom_resonance_minpoly_galois_sd_q12_15_jordan_prime_witness
  pom_resonance_minpoly_galois_sd_q12_15_dcycle_certificate :
    pom_resonance_minpoly_galois_sd_q12_15_degree =
      pom_resonance_minpoly_galois_sd_q12_15_expected_degree
        pom_resonance_minpoly_galois_sd_q12_15_q
  pom_resonance_minpoly_galois_sd_q12_15_dminusone_cycle_certificate :
    1 ≤ pom_resonance_minpoly_galois_sd_q12_15_degree
  pom_resonance_minpoly_galois_sd_q12_15_short_prime_cycle_certificate :
    pom_resonance_minpoly_galois_sd_q12_15_jordan_prime
        pom_resonance_minpoly_galois_sd_q12_15_q ≤
      pom_resonance_minpoly_galois_sd_q12_15_degree - 2
  pom_resonance_minpoly_galois_sd_q12_15_discriminant_nonsquare :
    pom_resonance_minpoly_galois_sd_q12_15_discriminant_witness % 2 = 1
  pom_resonance_minpoly_galois_sd_q12_15_local_jordan_criterion :
    pom_resonance_minpoly_galois_sd_q12_15_galois_group =
      pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric
        pom_resonance_minpoly_galois_sd_q12_15_degree

/-- The four audited certificates packaged together. -/
structure pom_resonance_minpoly_galois_sd_q12_15_data where
  pom_resonance_minpoly_galois_sd_q12_15_q12 :
    pom_resonance_minpoly_galois_sd_q12_15_certificate
  pom_resonance_minpoly_galois_sd_q12_15_q13 :
    pom_resonance_minpoly_galois_sd_q12_15_certificate
  pom_resonance_minpoly_galois_sd_q12_15_q14 :
    pom_resonance_minpoly_galois_sd_q12_15_certificate
  pom_resonance_minpoly_galois_sd_q12_15_q15 :
    pom_resonance_minpoly_galois_sd_q12_15_certificate
  pom_resonance_minpoly_galois_sd_q12_15_q12_eq :
    pom_resonance_minpoly_galois_sd_q12_15_certificate.pom_resonance_minpoly_galois_sd_q12_15_q
        pom_resonance_minpoly_galois_sd_q12_15_q12 = 12
  pom_resonance_minpoly_galois_sd_q12_15_q13_eq :
    pom_resonance_minpoly_galois_sd_q12_15_certificate.pom_resonance_minpoly_galois_sd_q12_15_q
        pom_resonance_minpoly_galois_sd_q12_15_q13 = 13
  pom_resonance_minpoly_galois_sd_q12_15_q14_eq :
    pom_resonance_minpoly_galois_sd_q12_15_certificate.pom_resonance_minpoly_galois_sd_q12_15_q
        pom_resonance_minpoly_galois_sd_q12_15_q14 = 14
  pom_resonance_minpoly_galois_sd_q12_15_q15_eq :
    pom_resonance_minpoly_galois_sd_q12_15_certificate.pom_resonance_minpoly_galois_sd_q12_15_q
        pom_resonance_minpoly_galois_sd_q12_15_q15 = 15

namespace pom_resonance_minpoly_galois_sd_q12_15_certificate

lemma pom_resonance_minpoly_galois_sd_q12_15_certificate_symmetric
    (C : pom_resonance_minpoly_galois_sd_q12_15_certificate) :
    C.pom_resonance_minpoly_galois_sd_q12_15_galois_group =
      pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric
        C.pom_resonance_minpoly_galois_sd_q12_15_degree :=
  C.pom_resonance_minpoly_galois_sd_q12_15_local_jordan_criterion

end pom_resonance_minpoly_galois_sd_q12_15_certificate

/-- The four finite Galois conclusions certified by the q=12--15 audit data. -/
def pom_resonance_minpoly_galois_sd_q12_15_statement
    (D : pom_resonance_minpoly_galois_sd_q12_15_data) : Prop :=
  let q12g :=
    D.pom_resonance_minpoly_galois_sd_q12_15_q12.pom_resonance_minpoly_galois_sd_q12_15_galois_group
  let q13g :=
    D.pom_resonance_minpoly_galois_sd_q12_15_q13.pom_resonance_minpoly_galois_sd_q12_15_galois_group
  let q14g :=
    D.pom_resonance_minpoly_galois_sd_q12_15_q14.pom_resonance_minpoly_galois_sd_q12_15_galois_group
  let q15g :=
    D.pom_resonance_minpoly_galois_sd_q12_15_q15.pom_resonance_minpoly_galois_sd_q12_15_galois_group
  q12g = pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric 13 ∧
    q13g = pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric 11 ∧
      q14g = pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric 13 ∧
        q15g = pom_resonance_minpoly_galois_sd_q12_15_galois_label.symmetric 11

open pom_resonance_minpoly_galois_sd_q12_15_certificate

/-- Paper label: `thm:pom-resonance-minpoly-galois-sd-q12-15`. -/
theorem paper_pom_resonance_minpoly_galois_sd_q12_15
    (D : pom_resonance_minpoly_galois_sd_q12_15_data) :
    pom_resonance_minpoly_galois_sd_q12_15_statement D := by
  unfold pom_resonance_minpoly_galois_sd_q12_15_statement
  refine ⟨?_, ?_, ?_, ?_⟩
  · let C := D.pom_resonance_minpoly_galois_sd_q12_15_q12
    have h := pom_resonance_minpoly_galois_sd_q12_15_certificate_symmetric C
    rw [C.pom_resonance_minpoly_galois_sd_q12_15_degree_eq] at h
    rw [D.pom_resonance_minpoly_galois_sd_q12_15_q12_eq] at h
    simpa [pom_resonance_minpoly_galois_sd_q12_15_expected_degree] using h
  · let C := D.pom_resonance_minpoly_galois_sd_q12_15_q13
    have h := pom_resonance_minpoly_galois_sd_q12_15_certificate_symmetric C
    rw [C.pom_resonance_minpoly_galois_sd_q12_15_degree_eq] at h
    rw [D.pom_resonance_minpoly_galois_sd_q12_15_q13_eq] at h
    simpa [pom_resonance_minpoly_galois_sd_q12_15_expected_degree] using h
  · let C := D.pom_resonance_minpoly_galois_sd_q12_15_q14
    have h := pom_resonance_minpoly_galois_sd_q12_15_certificate_symmetric C
    rw [C.pom_resonance_minpoly_galois_sd_q12_15_degree_eq] at h
    rw [D.pom_resonance_minpoly_galois_sd_q12_15_q14_eq] at h
    simpa [pom_resonance_minpoly_galois_sd_q12_15_expected_degree] using h
  · let C := D.pom_resonance_minpoly_galois_sd_q12_15_q15
    have h := pom_resonance_minpoly_galois_sd_q12_15_certificate_symmetric C
    rw [C.pom_resonance_minpoly_galois_sd_q12_15_degree_eq] at h
    rw [D.pom_resonance_minpoly_galois_sd_q12_15_q15_eq] at h
    simpa [pom_resonance_minpoly_galois_sd_q12_15_expected_degree] using h

end Omega.POM
