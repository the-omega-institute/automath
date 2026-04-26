import Mathlib.Data.Complex.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

namespace Omega.Zeta

/-- The audited Cayley-side scaling map. -/
def xi_cayley_scaling_no_finite_interior_invariant_set_scaled (m : ℝ) (z : ℂ) : ℂ :=
  (m : ℂ) * z

/-- A finite interior set is invariant when every point lies in the upper half-plane and its
forward Cayley-scaling image stays inside the set. -/
def xi_cayley_scaling_no_finite_interior_invariant_set_invariant (A : Finset ℂ) (m : ℝ) : Prop :=
  1 < m ∧
    ∀ z ∈ A, 0 < z.im ∧ xi_cayley_scaling_no_finite_interior_invariant_set_scaled m z ∈ A

private lemma xi_cayley_scaling_no_finite_interior_invariant_set_normSq_pos {z : ℂ}
    (hz : 0 < z.im) : 0 < Complex.normSq z := by
  have himsq : 0 < z.im * z.im := by nlinarith
  nlinarith [Complex.im_sq_le_normSq z]

private lemma xi_cayley_scaling_no_finite_interior_invariant_set_normSq_strict_growth
    {m : ℝ} {z : ℂ} (hm : 1 < m) (hz : 0 < z.im) :
    Complex.normSq z <
      Complex.normSq (xi_cayley_scaling_no_finite_interior_invariant_set_scaled m z) := by
  have hm_sq : 1 < m * m := by nlinarith
  have hzsq : 0 < Complex.normSq z :=
    xi_cayley_scaling_no_finite_interior_invariant_set_normSq_pos hz
  have hgrow : Complex.normSq z < (m * m) * Complex.normSq z := by nlinarith
  rw [xi_cayley_scaling_no_finite_interior_invariant_set_scaled, Complex.normSq_mul,
    Complex.normSq_ofReal]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hgrow

/-- A nonempty finite upper-half-plane set cannot be forward invariant under multiplication by a
real factor `m > 1`: the point with maximal squared norm is sent to a strictly larger one.
    thm:xi-cayley-scaling-no-finite-interior-invariant-set -/
theorem paper_xi_cayley_scaling_no_finite_interior_invariant_set (A : Finset ℂ) (m : ℝ)
    (h : xi_cayley_scaling_no_finite_interior_invariant_set_invariant A m) : A = ∅ := by
  rcases h with ⟨hm, hA⟩
  by_contra hne
  have hAne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
  obtain ⟨z, hzA, hmax⟩ := Finset.exists_max_image A Complex.normSq hAne
  obtain ⟨hzIm, hzScaled⟩ := hA z hzA
  have hle : Complex.normSq
      (xi_cayley_scaling_no_finite_interior_invariant_set_scaled m z) ≤ Complex.normSq z :=
    hmax _ hzScaled
  exact
    (not_le_of_gt
      (xi_cayley_scaling_no_finite_interior_invariant_set_normSq_strict_growth hm hzIm)) hle

end Omega.Zeta
