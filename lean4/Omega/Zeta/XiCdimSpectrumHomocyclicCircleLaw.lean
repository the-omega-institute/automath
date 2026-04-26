import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open scoped BigOperators

/-- The finite-spectrum polynomial for the homocyclic torsion group `(ℤ/nℤ)^m`. -/
noncomputable def xi_cdim_spectrum_homocyclic_circle_law_poly (n m : ℕ) (z : ℂ) : ℂ :=
  Finset.sum (Finset.range (m + 1)) (fun k => z ^ k * (n : ℂ) ^ (m - k))

lemma xi_cdim_spectrum_homocyclic_circle_law_poly_mul_sub
    (n m : ℕ) (z : ℂ) :
    xi_cdim_spectrum_homocyclic_circle_law_poly n m z * (z - n) =
      z ^ (m + 1) - (n : ℂ) ^ (m + 1) := by
  simpa [xi_cdim_spectrum_homocyclic_circle_law_poly] using
    geom_sum₂_mul z (n : ℂ) (m + 1)

lemma xi_cdim_spectrum_homocyclic_circle_law_poly_at_radius
    (n m : ℕ) :
    xi_cdim_spectrum_homocyclic_circle_law_poly n m n = (m + 1 : ℂ) * (n : ℂ) ^ m := by
  simpa [xi_cdim_spectrum_homocyclic_circle_law_poly] using geom_sum₂_self (n : ℂ) (m + 1)

lemma xi_cdim_spectrum_homocyclic_circle_law_poly_ne_zero_at_radius
    (n m : ℕ) (hn : 1 < n) :
    xi_cdim_spectrum_homocyclic_circle_law_poly n m n ≠ 0 := by
  have hn0_nat : n ≠ 0 := by omega
  have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn0_nat
  rw [xi_cdim_spectrum_homocyclic_circle_law_poly_at_radius]
  exact mul_ne_zero (by exact_mod_cast Nat.succ_ne_zero m) (pow_ne_zero _ hn0)

/-- Paper label: `cor:xi-cdim-spectrum-homocyclic-circle-law`. The homocyclic finite-spectrum
polynomial satisfies the geometric-series telescoping identity
`P(z) * (z - n) = z^(m+1) - n^(m+1)`, hence its zeros are exactly the nontrivial rescaled
`(m + 1)`st roots of unity. -/
theorem paper_xi_cdim_spectrum_homocyclic_circle_law (n m : ℕ) (hn : 1 < n) :
    let P := xi_cdim_spectrum_homocyclic_circle_law_poly n m
    (∀ z : ℂ, P z * (z - n) = z ^ (m + 1) - (n : ℂ) ^ (m + 1)) ∧
      ∀ z : ℂ, P z = 0 ↔ (z / n) ^ (m + 1) = 1 ∧ z ≠ n := by
  dsimp
  constructor
  · intro z
    exact xi_cdim_spectrum_homocyclic_circle_law_poly_mul_sub n m z
  · intro z
    have hn0_nat : n ≠ 0 := by omega
    have hn0 : (n : ℂ) ≠ 0 := by exact_mod_cast hn0_nat
    constructor
    · intro hz
      have hmul :
          xi_cdim_spectrum_homocyclic_circle_law_poly n m z * (z - n) = 0 := by
        rw [hz, zero_mul]
      have hpow :
          z ^ (m + 1) = (n : ℂ) ^ (m + 1) := by
        have hpoly := xi_cdim_spectrum_homocyclic_circle_law_poly_mul_sub n m z
        rw [hmul] at hpoly
        exact sub_eq_zero.mp hpoly.symm
      have hzne : z ≠ n := by
        intro hEq
        have hzero := xi_cdim_spectrum_homocyclic_circle_law_poly_ne_zero_at_radius n m hn
        exact hzero (hEq ▸ hz)
      refine ⟨?_, hzne⟩
      rw [div_pow, div_eq_iff (pow_ne_zero _ hn0)]
      simp [hpow]
    · rintro ⟨hzpow, hzne⟩
      have hpow :
          z ^ (m + 1) = (n : ℂ) ^ (m + 1) := by
        rw [div_pow, div_eq_iff (pow_ne_zero _ hn0)] at hzpow
        simp at hzpow
        exact hzpow
      have hmul :
          xi_cdim_spectrum_homocyclic_circle_law_poly n m z * (z - n) = 0 := by
        rw [xi_cdim_spectrum_homocyclic_circle_law_poly_mul_sub, hpow, sub_self]
      have hsub : z - n ≠ 0 := sub_ne_zero.mpr hzne
      exact Or.resolve_right (mul_eq_zero.mp hmul) hsub

end Omega.Zeta
