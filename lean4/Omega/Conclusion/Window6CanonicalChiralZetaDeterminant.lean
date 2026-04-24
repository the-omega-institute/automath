import Mathlib.Tactic
import Omega.GU.Window6ChiralSectorQ4Spectrum

namespace Omega.Conclusion

/-- The Laplacian spectral `ζ`-sum carried by the canonical window-6 chiral block. -/
noncomputable def conclusion_window6_canonical_chiral_zeta_determinant_laplacian_zeta
    (s : ℕ) : ℚ :=
  (1 : ℚ) / 2 ^ s + 4 / 4 ^ s + 6 / 6 ^ s + 4 / 8 ^ s + 1 / 10 ^ s

/-- The Laplacian determinant attached to the canonical window-6 chiral block. -/
def conclusion_window6_canonical_chiral_zeta_determinant_determinant : ℕ :=
  2 * 4 ^ 4 * 6 ^ 6 * 8 ^ 4 * 10

/-- Paper-facing window-6 chiral `ζ`/determinant package: the anti-invariant sector has
dimension `16`, carries the standard `Q₄` binomial spectrum, the Laplacian `ζ`-sum is the
five-term closed form coming from the shifted eigenvalues `{2, 4, 6, 8, 10}`, and the resulting
determinant is the expected product of those eigenvalues with multiplicity. -/
def conclusion_window6_canonical_chiral_zeta_determinant_statement : Prop :=
  Omega.GU.paper_window6_chiral_compression_hypercube_adjacency_stmt 6 ∧
    Omega.GU.window6WalshMinusBasisCardinality 6 = 16 ∧
    Omega.GU.window6ChiralSectorQ4SpectrumBinomialForm ∧
    (∀ s : ℕ,
      conclusion_window6_canonical_chiral_zeta_determinant_laplacian_zeta s =
        (Nat.choose 4 0 : ℚ) / 2 ^ s +
          (Nat.choose 4 1 : ℚ) / 4 ^ s +
          (Nat.choose 4 2 : ℚ) / 6 ^ s +
          (Nat.choose 4 3 : ℚ) / 8 ^ s +
          (Nat.choose 4 4 : ℚ) / 10 ^ s) ∧
    conclusion_window6_canonical_chiral_zeta_determinant_laplacian_zeta 0 = 16 ∧
    conclusion_window6_canonical_chiral_zeta_determinant_determinant =
      2 * 4 ^ 4 * 6 ^ 6 * 8 ^ 4 * 10

/-- Paper label: `thm:conclusion-window6-canonical-chiral-zeta-determinant`. -/
def paper_conclusion_window6_canonical_chiral_zeta_determinant : Prop :=
  conclusion_window6_canonical_chiral_zeta_determinant_statement

theorem conclusion_window6_canonical_chiral_zeta_determinant_verified :
    paper_conclusion_window6_canonical_chiral_zeta_determinant := by
  rcases Omega.GU.paper_window6_chiral_sector_q4_spectrum with ⟨hcomp, hcard, hbinom⟩
  refine ⟨hcomp, hcard, hbinom, ?_, ?_, rfl⟩
  · intro s
    norm_num [conclusion_window6_canonical_chiral_zeta_determinant_laplacian_zeta, Nat.choose]
  · norm_num [conclusion_window6_canonical_chiral_zeta_determinant_laplacian_zeta]

end Omega.Conclusion
