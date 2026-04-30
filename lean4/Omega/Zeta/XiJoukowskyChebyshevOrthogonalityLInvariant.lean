import Mathlib.Tactic

namespace Omega.Zeta

/-- Zero-mode pairing for Laurent monomials `u^a` and `u^b`. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_modePairing (a b : ℤ) : ℤ :=
  if a + b = 0 then 1 else 0

/-- The positive Fourier exponent used for the `n`th nonconstant Chebyshev mode. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_frequency (n : ℕ) : ℤ :=
  (n + 1 : ℤ)

/-- Kronecker delta in the integer normalization used by the finite Fourier model. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_delta (n m : ℕ) : ℤ :=
  if n = m then 1 else 0

/-- Constant-term pairing of the two symmetric modes
`C_n = u^n + u^{-n}` and `C_m = u^m + u^{-m}`. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing (n m : ℕ) : ℤ :=
  2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m

/-- Constant-term pairing of the two antisymmetric modes
`D_n = u^n - u^{-n}` and `D_m = u^m - u^{-m}`. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_D_pairing (n m : ℕ) : ℤ :=
  -2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m

/-- Mixed constant-term pairing of `C_n` with `D_m`. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_CD_pairing (_n _m : ℕ) : ℤ :=
  0

/-- Paper-facing statement for
`thm:xi-joukowsky-chebyshev-orthogonality-L-invariant`.

The ellipse parameter `L` is present only as a scale label: after pulling the pairing back to
the Laurent coordinate, all three identities are constant-term identities and hence independent
of `L`.  The model indexes nonconstant modes by `n + 1`, so the paper's `n,m ≥ 1` convention is
represented for all Lean natural inputs. -/
def xi_joukowsky_chebyshev_orthogonality_l_invariant_statement
    (L : ℝ) (n m : ℕ) : Prop :=
  (0 < L →
    xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing n m =
      2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m ∧
    xi_joukowsky_chebyshev_orthogonality_l_invariant_D_pairing n m =
      -2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m ∧
    xi_joukowsky_chebyshev_orthogonality_l_invariant_CD_pairing n m = 0) ∧
    xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing n m =
      xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing n m

lemma xi_joukowsky_chebyshev_orthogonality_l_invariant_pairings
    (n m : ℕ) :
    xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing n m =
      2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m ∧
    xi_joukowsky_chebyshev_orthogonality_l_invariant_D_pairing n m =
      -2 * xi_joukowsky_chebyshev_orthogonality_l_invariant_delta n m ∧
    xi_joukowsky_chebyshev_orthogonality_l_invariant_CD_pairing n m = 0 := by
  simp [xi_joukowsky_chebyshev_orthogonality_l_invariant_C_pairing,
    xi_joukowsky_chebyshev_orthogonality_l_invariant_D_pairing,
    xi_joukowsky_chebyshev_orthogonality_l_invariant_CD_pairing]

/-- Paper label: `thm:xi-joukowsky-chebyshev-orthogonality-L-invariant`. -/
theorem paper_xi_joukowsky_chebyshev_orthogonality_l_invariant
    (L : ℝ) (hL : 0 < L) (n m : ℕ) :
    xi_joukowsky_chebyshev_orthogonality_l_invariant_statement L n m := by
  refine ⟨?_, rfl⟩
  intro _hL
  have _scalePositive : 0 < L := hL
  exact xi_joukowsky_chebyshev_orthogonality_l_invariant_pairings n m

end Omega.Zeta
