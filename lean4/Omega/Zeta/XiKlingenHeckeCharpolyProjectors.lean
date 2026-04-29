import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Polynomial

/-- The three audited eigenvalues of the `40`-point orthogonal adjacency operator. -/
def xi_klingen_hecke_charpoly_projectors_spectrum : Finset ℚ :=
  insert 12 (insert 2 ({(-4 : ℚ)} : Finset ℚ))

/-- The minimal polynomial attached to the strongly-regular parameters `(40,12,2,4)`. -/
noncomputable def xi_klingen_hecke_charpoly_projectors_minimal_polynomial : Polynomial ℚ :=
  (X - C 12) * (X - C 2) * (X + C 4)

/-- The characteristic polynomial coming from multiplicities `1 + 24 + 15 = 40`. -/
noncomputable def xi_klingen_hecke_charpoly_projectors_characteristic_polynomial : Polynomial ℚ :=
  (X - C 12) * (X - C 2) ^ 24 * (X + C 4) ^ 15

/-- The Lagrange projector onto the `12`-eigenspace. -/
def xi_klingen_hecke_charpoly_projectors_e12 (t : ℚ) : ℚ :=
  ((t - 2) * (t + 4)) / 160

/-- The Lagrange projector onto the `2`-eigenspace. -/
def xi_klingen_hecke_charpoly_projectors_e2 (t : ℚ) : ℚ :=
  ((12 - t) * (t + 4)) / 60

/-- The Lagrange projector onto the `(-4)`-eigenspace. -/
def xi_klingen_hecke_charpoly_projectors_em4 (t : ℚ) : ℚ :=
  ((t - 12) * (t - 2)) / 96

/-- The multiplicity package of the three eigenvalues in the `40`-point model. -/
def xi_klingen_hecke_charpoly_projectors_multiplicity (t : ℚ) : ℕ :=
  if t = 12 then 1 else if t = 2 then 24 else if t = -4 then 15 else 0

/-- Membership in the finite spectrum is exactly membership in the three audited eigenvalues. -/
lemma xi_klingen_hecke_charpoly_projectors_mem_spectrum {t : ℚ}
    (ht : t ∈ xi_klingen_hecke_charpoly_projectors_spectrum) :
    t = 12 ∨ t = 2 ∨ t = -4 := by
  simpa [xi_klingen_hecke_charpoly_projectors_spectrum] using ht

/-- Paper label: `thm:xi-klingen-hecke-charpoly-projectors`. -/
theorem paper_xi_klingen_hecke_charpoly_projectors :
    xi_klingen_hecke_charpoly_projectors_minimal_polynomial =
        (X - C 12) * (X - C 2) * (X + C 4) ∧
      xi_klingen_hecke_charpoly_projectors_characteristic_polynomial =
        (X - C 12) * (X - C 2) ^ 24 * (X + C 4) ^ 15 ∧
      (∀ t ∈ xi_klingen_hecke_charpoly_projectors_spectrum,
        eval t xi_klingen_hecke_charpoly_projectors_minimal_polynomial = 0 ∧
          xi_klingen_hecke_charpoly_projectors_e12 t +
              xi_klingen_hecke_charpoly_projectors_e2 t +
              xi_klingen_hecke_charpoly_projectors_em4 t = 1 ∧
          (xi_klingen_hecke_charpoly_projectors_e12 t) ^ 2 =
              xi_klingen_hecke_charpoly_projectors_e12 t ∧
          (xi_klingen_hecke_charpoly_projectors_e2 t) ^ 2 =
              xi_klingen_hecke_charpoly_projectors_e2 t ∧
          (xi_klingen_hecke_charpoly_projectors_em4 t) ^ 2 =
              xi_klingen_hecke_charpoly_projectors_em4 t ∧
          xi_klingen_hecke_charpoly_projectors_e12 t *
              xi_klingen_hecke_charpoly_projectors_e2 t = 0 ∧
          xi_klingen_hecke_charpoly_projectors_e12 t *
              xi_klingen_hecke_charpoly_projectors_em4 t = 0 ∧
          xi_klingen_hecke_charpoly_projectors_e2 t *
              xi_klingen_hecke_charpoly_projectors_em4 t = 0) ∧
      xi_klingen_hecke_charpoly_projectors_multiplicity 12 = 1 ∧
      xi_klingen_hecke_charpoly_projectors_multiplicity 2 = 24 ∧
      xi_klingen_hecke_charpoly_projectors_multiplicity (-4) = 15 := by
  refine ⟨rfl, rfl, ?_, by
    norm_num [xi_klingen_hecke_charpoly_projectors_multiplicity], by
    norm_num [xi_klingen_hecke_charpoly_projectors_multiplicity], by
    norm_num [xi_klingen_hecke_charpoly_projectors_multiplicity]⟩
  intro t ht
  rcases xi_klingen_hecke_charpoly_projectors_mem_spectrum ht with rfl | rfl | rfl
  · norm_num [xi_klingen_hecke_charpoly_projectors_minimal_polynomial,
      xi_klingen_hecke_charpoly_projectors_e12,
      xi_klingen_hecke_charpoly_projectors_e2,
      xi_klingen_hecke_charpoly_projectors_em4]
  · norm_num [xi_klingen_hecke_charpoly_projectors_minimal_polynomial,
      xi_klingen_hecke_charpoly_projectors_e12,
      xi_klingen_hecke_charpoly_projectors_e2,
      xi_klingen_hecke_charpoly_projectors_em4]
  · norm_num [xi_klingen_hecke_charpoly_projectors_minimal_polynomial,
      xi_klingen_hecke_charpoly_projectors_e12,
      xi_klingen_hecke_charpoly_projectors_e2,
      xi_klingen_hecke_charpoly_projectors_em4]

end Omega.Zeta
