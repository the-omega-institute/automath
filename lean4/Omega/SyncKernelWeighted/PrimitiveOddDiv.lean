import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Degree.Operations
import Mathlib.Tactic

namespace Omega.SyncKernelWeighted

open Polynomial
open scoped Polynomial

/-- The reduced odd primitive polynomial obtained after dividing out the obvious `X` factor. -/
noncomputable def primitive_odd_div_reduced_poly (n : ℕ) : Polynomial ℤ :=
  (X + 1) ^ n

/-- The primitive polynomial carrying the visible `X`-factor. -/
noncomputable def primitive_odd_div_poly (n : ℕ) : Polynomial ℤ :=
  X * primitive_odd_div_reduced_poly n

lemma primitive_odd_div_reduced_poly_natDegree (n : ℕ) :
    (primitive_odd_div_reduced_poly n).natDegree = n := by
  simpa [primitive_odd_div_reduced_poly] using Polynomial.natDegree_pow_X_add_C n (1 : ℤ)

lemma primitive_odd_div_reduced_poly_isRoot_neg_one (n : ℕ) (hn : Odd n) :
    IsRoot (primitive_odd_div_reduced_poly n) (-1 : ℤ) := by
  change (primitive_odd_div_reduced_poly n).eval (-1 : ℤ) = 0
  have hn_pos : 0 < n := hn.pos
  simp [primitive_odd_div_reduced_poly, hn_pos.ne']

/-- Paper label: `cor:primitive-odd-div`.  For odd `n`, the reduced primitive polynomial has odd
degree and vanishes at `u = -1`, so `X + 1` divides the reduced polynomial and therefore
`X * (X + 1)` divides the full primitive polynomial. -/
theorem paper_primitive_odd_div (n : ℕ) (hn : Odd n) :
    Odd (primitive_odd_div_reduced_poly n).natDegree ∧
      X * (X + 1) ∣ primitive_odd_div_poly n := by
  have hroot : IsRoot (primitive_odd_div_reduced_poly n) (-1 : ℤ) :=
    primitive_odd_div_reduced_poly_isRoot_neg_one n hn
  have hX1 :
      X + 1 ∣ primitive_odd_div_reduced_poly n := by
    simpa [sub_eq_add_neg] using (Polynomial.dvd_iff_isRoot.mpr hroot)
  refine ⟨?_, ?_⟩
  · simpa [primitive_odd_div_reduced_poly_natDegree] using hn
  · rcases hX1 with ⟨Q, hQ⟩
    refine ⟨Q, ?_⟩
    calc
      primitive_odd_div_poly n = X * primitive_odd_div_reduced_poly n := by
        rfl
      _ = X * ((X + 1) * Q) := by rw [hQ]
      _ = X * (X + 1) * Q := by ring

end Omega.SyncKernelWeighted
