import Omega.TypedAddressBiaxialCompletion.ComovingFirstOrder

namespace Omega.TypedAddressBiaxialCompletion

/-- The inverse image in the upper half-plane of the Cayley modulus circle `|w| = ρ` is an
explicit Euclidean circle, with the stated intercepts on the imaginary axis.
    prop:app-cayley-preimage-modulus-circle -/
theorem paper_app_cayley_preimage_modulus_circle (rho : ℝ) (hrho0 : 0 < rho) (hrho1 : rho < 1) :
    let c := (1 + rho ^ 2) / (1 - rho ^ 2)
    let r := (2 * rho) / (1 - rho ^ 2)
    (∀ x y : ℝ, typedAddressCayleyModSq y x = rho ^ 2 ↔ x ^ 2 + (y - c) ^ 2 = r ^ 2) ∧
      c - r = (1 - rho) / (1 + rho) ∧ c + r = (1 + rho) / (1 - rho) := by
  dsimp
  have hrho2lt1 : rho ^ 2 < 1 := by nlinarith
  have hden_pos : 0 < 1 - rho ^ 2 := by nlinarith
  have hden_ne : 1 - rho ^ 2 ≠ 0 := by linarith
  have hrho2_pos : 0 < rho ^ 2 := by positivity
  have hone_add_ne : 1 + rho ≠ 0 := by linarith
  have hone_sub_ne : 1 - rho ≠ 0 := by linarith
  refine ⟨?_, ?_, ?_⟩
  · intro x y
    constructor
    · intro hmod
      have hxy_den_ne : x ^ 2 + (1 + y) ^ 2 ≠ 0 := by
        intro hzero
        have : (0 : ℝ) = rho ^ 2 := by
          simpa [typedAddressCayleyModSq, hzero] using hmod
        linarith
      have hpoly : x ^ 2 + (1 - y) ^ 2 = rho ^ 2 * (x ^ 2 + (1 + y) ^ 2) := by
        unfold typedAddressCayleyModSq at hmod
        field_simp [hxy_den_ne] at hmod
        linarith
      have hcircle : x ^ 2 + (y - (1 + rho ^ 2) / (1 - rho ^ 2)) ^ 2 =
          ((2 * rho) / (1 - rho ^ 2)) ^ 2 := by
        field_simp [hden_ne]
        ring_nf
        nlinarith [hpoly]
      simpa using hcircle
    · intro hcircle
      have hxy_den_ne : x ^ 2 + (1 + y) ^ 2 ≠ 0 := by
        intro hzero
        have hx_sq : x ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg (1 + y), hzero]
        have hy_sq : (1 + y) ^ 2 = 0 := by nlinarith [sq_nonneg x, sq_nonneg (1 + y), hzero]
        have hx : x = 0 := by nlinarith
        have hy : y = -1 := by nlinarith
        subst hx
        subst hy
        have : ((0 : ℝ) ^ 2 + (-1 - (1 + rho ^ 2) / (1 - rho ^ 2)) ^ 2) ≠
            (((2 * rho) / (1 - rho ^ 2)) ^ 2) := by
          intro hEq
          field_simp [hden_ne] at hEq
          nlinarith
        exact this hcircle
      have hpoly : x ^ 2 + (1 - y) ^ 2 = rho ^ 2 * (x ^ 2 + (1 + y) ^ 2) := by
        have hcircle' := hcircle
        field_simp [hden_ne] at hcircle'
        nlinarith [hcircle']
      unfold typedAddressCayleyModSq
      field_simp [hxy_den_ne]
      linarith
  · field_simp [hden_ne, hone_add_ne]
    ring
  · field_simp [hden_ne, hone_sub_ne]
    ring

end Omega.TypedAddressBiaxialCompletion
