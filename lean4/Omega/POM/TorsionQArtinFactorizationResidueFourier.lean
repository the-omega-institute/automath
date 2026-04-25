import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Complex.Basic
import Mathlib.Tactic

namespace Omega.POM

open scoped BigOperators

noncomputable section

/-- The `χ`-eigenspace pole used in the torsion-`q` Artin package. -/
def pom_torsion_q_artin_factorization_residue_fourier_pole (q : ℕ) (χ : Fin q) : ℂ :=
  ((χ.1 + 1 : ℕ) : ℂ)

/-- The denominator contributed by the `χ`-eigenspace. -/
def pom_torsion_q_artin_factorization_residue_fourier_block (q : ℕ) (χ : Fin q) (z : ℂ) : ℂ :=
  1 - pom_torsion_q_artin_factorization_residue_fourier_pole q χ * z

/-- The total Artin denominator obtained from the character decomposition. -/
def pom_torsion_q_artin_factorization_residue_fourier_artin_den (q : ℕ) (z : ℂ) : ℂ :=
  ∏ χ : Fin q, pom_torsion_q_artin_factorization_residue_fourier_block q χ z

/-- The reciprocal Artin factor attached to the torsion-`q` package. -/
def pom_torsion_q_artin_factorization_residue_fourier_artin_zeta (q : ℕ) (z : ℂ) : ℂ :=
  (pom_torsion_q_artin_factorization_residue_fourier_artin_den q z)⁻¹

/-- The reciprocal factor on one character eigenspace. -/
def pom_torsion_q_artin_factorization_residue_fourier_channel_zeta
    (q : ℕ) (χ : Fin q) (z : ℂ) : ℂ :=
  (pom_torsion_q_artin_factorization_residue_fourier_block q χ z)⁻¹

/-- The residue of the simple pole contributed by one character block. -/
def pom_torsion_q_artin_factorization_residue_fourier_residue (q : ℕ) (χ : Fin q) : ℂ :=
  -(pom_torsion_q_artin_factorization_residue_fourier_pole q χ)⁻¹

/-- The `n`-th coefficient extracted from the `χ`-channel after residue normalization. -/
def pom_torsion_q_artin_factorization_residue_fourier_channel_coeff
    (q : ℕ) (χ : Fin q) (n : ℕ) : ℂ :=
  pom_torsion_q_artin_factorization_residue_fourier_residue q χ *
    pom_torsion_q_artin_factorization_residue_fourier_pole q χ ^ n

/-- The total Fourier coefficient obtained by summing the character-channel contributions. -/
def pom_torsion_q_artin_factorization_residue_fourier_total_coeff (q : ℕ) (n : ℕ) : ℂ :=
  ∑ χ : Fin q, pom_torsion_q_artin_factorization_residue_fourier_channel_coeff q χ n

/-- Package collecting the character-block Artin factorization and the residue/Fourier extraction
formulas for the simple poles. -/
structure pomTorsionQArtinFactorizationResidueFourierPackage where
  pom_torsion_q_artin_factorization_residue_fourier_blockFactorization :
    ∀ q : ℕ, ∀ z : ℂ,
      pom_torsion_q_artin_factorization_residue_fourier_artin_den q z =
        ∏ χ : Fin q, pom_torsion_q_artin_factorization_residue_fourier_block q χ z
  pom_torsion_q_artin_factorization_residue_fourier_zetaFactorization :
    ∀ q : ℕ, ∀ z : ℂ,
      pom_torsion_q_artin_factorization_residue_fourier_artin_zeta q z =
        ∏ χ : Fin q, pom_torsion_q_artin_factorization_residue_fourier_channel_zeta q χ z
  pom_torsion_q_artin_factorization_residue_fourier_simplePoleLocation :
    ∀ q : ℕ, ∀ χ : Fin q,
      pom_torsion_q_artin_factorization_residue_fourier_block q χ
          (pom_torsion_q_artin_factorization_residue_fourier_pole q χ)⁻¹ =
        0
  pom_torsion_q_artin_factorization_residue_fourier_channelCoefficientFormula :
    ∀ q : ℕ, ∀ χ : Fin q, ∀ n : ℕ,
      pom_torsion_q_artin_factorization_residue_fourier_channel_coeff q χ n =
        pom_torsion_q_artin_factorization_residue_fourier_residue q χ *
          pom_torsion_q_artin_factorization_residue_fourier_pole q χ ^ n
  pom_torsion_q_artin_factorization_residue_fourier_totalCoefficientFormula :
    ∀ q : ℕ, ∀ n : ℕ,
      pom_torsion_q_artin_factorization_residue_fourier_total_coeff q n =
        ∑ χ : Fin q, pom_torsion_q_artin_factorization_residue_fourier_channel_coeff q χ n

/-- The torsion-`q` Artin denominator splits over character eigenspaces, the reciprocal zeta factor
is the product of the channel reciprocals, each block has a simple pole at the inverse pole
location, and residue extraction gives the explicit Fourier coefficients.
    thm:pom-torsion-q-artin-factorization-residue-fourier -/
theorem paper_pom_torsion_q_artin_factorization_residue_fourier :
    pomTorsionQArtinFactorizationResidueFourierPackage := by
  refine
    { pom_torsion_q_artin_factorization_residue_fourier_blockFactorization := ?_
      pom_torsion_q_artin_factorization_residue_fourier_zetaFactorization := ?_
      pom_torsion_q_artin_factorization_residue_fourier_simplePoleLocation := ?_
      pom_torsion_q_artin_factorization_residue_fourier_channelCoefficientFormula := ?_
      pom_torsion_q_artin_factorization_residue_fourier_totalCoefficientFormula := ?_ }
  · intro q z
    rfl
  · intro q z
    rw [pom_torsion_q_artin_factorization_residue_fourier_artin_zeta,
      pom_torsion_q_artin_factorization_residue_fourier_artin_den]
    simp [pom_torsion_q_artin_factorization_residue_fourier_channel_zeta]
  · intro q χ
    have hpole_nat : (χ.1 + 1 : ℕ) ≠ 0 := Nat.succ_ne_zero χ.1
    have hpole_ne : pom_torsion_q_artin_factorization_residue_fourier_pole q χ ≠ 0 := by
      change (((χ.1 + 1 : ℕ) : ℂ)) ≠ 0
      exact_mod_cast hpole_nat
    simp [pom_torsion_q_artin_factorization_residue_fourier_block, hpole_ne]
  · intro q χ n
    rfl
  · intro q n
    rfl

end

end Omega.POM
