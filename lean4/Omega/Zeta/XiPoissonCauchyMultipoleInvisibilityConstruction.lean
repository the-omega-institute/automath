import Mathlib.RingTheory.RootsOfUnity.Complex
import Mathlib.Tactic

namespace Omega.Zeta

open Finset

noncomputable section

/-- The primitive `N`-th root used for the regular `N`-gon witness. -/
def xi_poisson_cauchy_multipole_invisibility_construction_root (N : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / N)

/-- The radius-`r` regular `N`-gon point indexed by `j`. -/
def xi_poisson_cauchy_multipole_invisibility_construction_point (N : ℕ) (r : ℝ)
    (j : Fin N) : ℂ :=
  (r : ℂ) * xi_poisson_cauchy_multipole_invisibility_construction_root N ^ (j : ℕ)

/-- The `k`-th complex moment of the regular `N`-gon witness. -/
def xi_poisson_cauchy_multipole_invisibility_construction_moment (N : ℕ) (r : ℝ)
    (k : ℕ) : ℂ :=
  ∑ j : Fin N, xi_poisson_cauchy_multipole_invisibility_construction_point N r j ^ k

/-- Concrete package for the regular `N`-gon multipole-invisibility construction. -/
def xi_poisson_cauchy_multipole_invisibility_construction_package (N : ℕ) (r : ℝ) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < N →
    xi_poisson_cauchy_multipole_invisibility_construction_moment N r k = 0) ∧
  xi_poisson_cauchy_multipole_invisibility_construction_moment N r N =
    (N : ℂ) * (r : ℂ) ^ N ∧
  2 ≤ N ∧ 0 < r

lemma xi_poisson_cauchy_multipole_invisibility_construction_geom_sum_eq_zero
    {N k : ℕ} {ζ : ℂ} (hζ : IsPrimitiveRoot ζ N) (hk0 : k ≠ 0) (hkN : k < N) :
    (∑ j ∈ Finset.range N, (ζ ^ k) ^ j) = 0 := by
  have hpow : (ζ ^ k) ^ N = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hne : ζ ^ k ≠ 1 := hζ.pow_ne_one_of_pos_of_lt hk0 hkN
  have hmul : (∑ j ∈ Finset.range N, (ζ ^ k) ^ j) * (ζ ^ k - 1) = 0 := by
    simpa [hpow] using geom_sum_mul (ζ ^ k) N
  exact (mul_eq_zero.mp hmul).resolve_right (sub_ne_zero.mpr hne)

lemma xi_poisson_cauchy_multipole_invisibility_construction_moment_vanish
    {N k : ℕ} {r : ℝ} (hN : 2 ≤ N) (hk1 : 1 ≤ k) (hkN : k < N) :
    xi_poisson_cauchy_multipole_invisibility_construction_moment N r k = 0 := by
  classical
  have hN0 : N ≠ 0 := by omega
  have hk0 : k ≠ 0 := by omega
  let ζ := xi_poisson_cauchy_multipole_invisibility_construction_root N
  have hζ : IsPrimitiveRoot ζ N := by
    simpa [ζ, xi_poisson_cauchy_multipole_invisibility_construction_root] using
      Complex.isPrimitiveRoot_exp N hN0
  have hgeom :
      (∑ j ∈ Finset.range N, (ζ ^ k) ^ j) = 0 :=
    xi_poisson_cauchy_multipole_invisibility_construction_geom_sum_eq_zero hζ hk0 hkN
  have hgeomFin : (∑ j : Fin N, (ζ ^ k) ^ (j : ℕ)) = 0 := by
    simpa [Fin.sum_univ_eq_sum_range] using hgeom
  rw [xi_poisson_cauchy_multipole_invisibility_construction_moment]
  simp_rw [xi_poisson_cauchy_multipole_invisibility_construction_point]
  calc
    (∑ x : Fin N,
        ((r : ℂ) *
          xi_poisson_cauchy_multipole_invisibility_construction_root N ^ (x : ℕ)) ^ k) =
        (r : ℂ) ^ k *
          ∑ x : Fin N,
            (xi_poisson_cauchy_multipole_invisibility_construction_root N ^ k) ^
              (x : ℕ) := by
      simp_rw [mul_pow, ← pow_mul]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro x hx
      rw [mul_comm k (x : ℕ)]
    _ = 0 := by
      simp [ζ, hgeomFin]

lemma xi_poisson_cauchy_multipole_invisibility_construction_moment_top
    {N : ℕ} {r : ℝ} (hN : 2 ≤ N) :
    xi_poisson_cauchy_multipole_invisibility_construction_moment N r N =
      (N : ℂ) * (r : ℂ) ^ N := by
  classical
  have hN0 : N ≠ 0 := by omega
  let ζ := xi_poisson_cauchy_multipole_invisibility_construction_root N
  have hζ : IsPrimitiveRoot ζ N := by
    simpa [ζ, xi_poisson_cauchy_multipole_invisibility_construction_root] using
      Complex.isPrimitiveRoot_exp N hN0
  rw [xi_poisson_cauchy_multipole_invisibility_construction_moment]
  simp_rw [xi_poisson_cauchy_multipole_invisibility_construction_point]
  calc
    (∑ x : Fin N,
        ((r : ℂ) *
          xi_poisson_cauchy_multipole_invisibility_construction_root N ^ (x : ℕ)) ^ N) =
        ∑ _x : Fin N, (r : ℂ) ^ N := by
      refine Finset.sum_congr rfl ?_
      intro x hx
      have hroot :
          xi_poisson_cauchy_multipole_invisibility_construction_root N ^ N = 1 := by
        simpa [ζ] using hζ.pow_eq_one
      have hxpow :
          (xi_poisson_cauchy_multipole_invisibility_construction_root N ^ (x : ℕ)) ^ N =
            1 := by
        rw [← pow_mul, Nat.mul_comm (x : ℕ) N, pow_mul, hroot, one_pow]
      rw [mul_pow, hxpow, mul_one]
    _ = (N : ℂ) * (r : ℂ) ^ N := by
      simp [mul_comm]

/-- Paper label: `prop:xi-poisson-cauchy-multipole-invisibility-construction`. -/
theorem paper_xi_poisson_cauchy_multipole_invisibility_construction (N : ℕ) (hN : 2 ≤ N)
    (r : ℝ) (hr : 0 < r) :
    xi_poisson_cauchy_multipole_invisibility_construction_package N r := by
  exact ⟨
    fun k hk1 hkN =>
      xi_poisson_cauchy_multipole_invisibility_construction_moment_vanish hN hk1 hkN,
    xi_poisson_cauchy_multipole_invisibility_construction_moment_top hN,
    hN,
    hr⟩

end

end Omega.Zeta
