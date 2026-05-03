import Mathlib.Data.Real.Basic

namespace Omega.Zeta

/-- A finite pulled-back Cayley boundary measure model, recorded by its masses on a
geometric sequence of disjoint annuli.  The endpoint atoms are kept separately; the
annuli represent the non-endpoint part of the boundary chart. -/
structure xi_cayley_dilation_invariant_measure_endpoint_atomic_finite_invariant_measure where
  annulusMass : ℕ → ℝ
  endpointMinusMass : ℝ
  endpointPlusMass : ℝ
  dilationInvariant : ∀ k : ℕ, annulusMass (k + 1) = annulusMass k
  finiteDisjointSupport : ∃ N : ℕ, annulusMass N = 0

/-- Endpoint atomicity in the finite annulus model: every non-endpoint annulus has zero mass. -/
def xi_cayley_dilation_invariant_measure_endpoint_atomic_endpoint_atomic_decomposition
    (M : xi_cayley_dilation_invariant_measure_endpoint_atomic_finite_invariant_measure) :
    Prop :=
  ∀ k : ℕ, M.annulusMass k = 0

lemma xi_cayley_dilation_invariant_measure_endpoint_atomic_annulus_constant
    (M : xi_cayley_dilation_invariant_measure_endpoint_atomic_finite_invariant_measure) :
    ∀ k : ℕ, M.annulusMass k = M.annulusMass 0 := by
  intro k
  induction k with
  | zero =>
      rfl
  | succ k ih =>
      calc
        M.annulusMass (k + 1) = M.annulusMass k := M.dilationInvariant k
        _ = M.annulusMass 0 := ih

/-- Paper label: `prop:xi-cayley-dilation-invariant-measure-endpoint-atomic`. -/
theorem paper_xi_cayley_dilation_invariant_measure_endpoint_atomic
    (M : xi_cayley_dilation_invariant_measure_endpoint_atomic_finite_invariant_measure) :
    xi_cayley_dilation_invariant_measure_endpoint_atomic_endpoint_atomic_decomposition M := by
  rcases M.finiteDisjointSupport with ⟨N, hN⟩
  intro k
  calc
    M.annulusMass k = M.annulusMass 0 :=
      xi_cayley_dilation_invariant_measure_endpoint_atomic_annulus_constant M k
    _ = M.annulusMass N :=
      (xi_cayley_dilation_invariant_measure_endpoint_atomic_annulus_constant M N).symm
    _ = 0 := hN

end Omega.Zeta
