import Mathlib.Tactic

namespace Omega.Zeta

/-- Coordinatewise bounded CRT uniqueness for integer Hankel minor coordinates. -/
lemma xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction_bounded_crt_unique
    (B P : ℕ) (hP : 2 * B < P) (x y : ℤ)
    (hx : -(B : ℤ) ≤ x ∧ x ≤ B) (hy : -(B : ℤ) ≤ y ∧ y ≤ B)
    (hcong : (P : ℤ) ∣ x - y) :
    x = y := by
  have hP_pos_nat : 0 < P := by omega
  have hP_pos_int : (0 : ℤ) < (P : ℤ) := by exact_mod_cast hP_pos_nat
  have hdiff_upper : x - y ≤ 2 * (B : ℤ) := by linarith [hx.2, hy.1]
  have hdiff_lower : -(2 * (B : ℤ)) ≤ x - y := by linarith [hx.1, hy.2]
  have habs_le : |x - y| ≤ 2 * (B : ℤ) := abs_le.2 ⟨hdiff_lower, hdiff_upper⟩
  have hbound : 2 * (B : ℤ) < (P : ℤ) := by exact_mod_cast hP
  have habs_lt : |x - y| < (P : ℤ) := lt_of_le_of_lt habs_le hbound
  rcases hcong with ⟨k, hk⟩
  have hk_zero : k = 0 := by
    by_contra hk_ne
    have hk_abs_ge_one : (1 : ℤ) ≤ |k| := by
      have hk_abs_pos : (0 : ℤ) < |k| := abs_pos.mpr hk_ne
      omega
    have hP_le_mul : (P : ℤ) ≤ (P : ℤ) * |k| := by nlinarith
    have hP_le_abs : (P : ℤ) ≤ |x - y| := by
      calc
        (P : ℤ) ≤ (P : ℤ) * |k| := hP_le_mul
        _ = |(P : ℤ) * k| := by
          rw [abs_mul, abs_of_nonneg (le_of_lt hP_pos_int)]
        _ = |x - y| := by rw [hk]
    exact (not_lt_of_ge hP_le_abs) habs_lt
  have hzero : x - y = 0 := by simpa [hk_zero] using hk
  exact sub_eq_zero.mp hzero

/-- Concrete statement for
`cor:xi-hankel-maxminor-height-bound-deterministic-crt-reconstruction`.

The coordinates `det` are the integer maximal-minor syndrome coordinates, `recon` is the bounded
CRT reconstruction, and `minor = cof * det` records determinant-coordinate consistency. -/
def xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction_statement : Prop :=
  ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (B P : ℕ)
    (minor cof det recon : ι → ℤ),
    2 * B < P →
      (∀ i, -(B : ℤ) ≤ det i ∧ det i ≤ B) →
      (∀ i, -(B : ℤ) ≤ recon i ∧ recon i ≤ B) →
      (∀ i, (P : ℤ) ∣ recon i - det i) →
      (∀ i, minor i = cof i * det i) →
      (∀ i, recon i = det i) ∧ (∀ i, minor i = cof i * recon i)

/-- Paper label: `cor:xi-hankel-maxminor-height-bound-deterministic-crt-reconstruction`. -/
theorem paper_xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction :
    xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction_statement := by
  intro ι _ _ B P minor cof det recon hP hdet hrecon hcong hminor
  constructor
  · intro i
    exact xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction_bounded_crt_unique
      B P hP (recon i) (det i) (hrecon i) (hdet i) (hcong i)
  · intro i
    rw [hminor i]
    congr 1
    exact (xi_hankel_maxminor_height_bound_deterministic_crt_reconstruction_bounded_crt_unique
      B P hP (recon i) (det i) (hrecon i) (hdet i) (hcong i)).symm

end Omega.Zeta
