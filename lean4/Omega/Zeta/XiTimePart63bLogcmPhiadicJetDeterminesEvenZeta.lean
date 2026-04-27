import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete finite-stage data for recovering Bernoulli coefficients from a `φ`-adic logarithmic
CM jet and then transporting those coefficients to even zeta values. -/
structure xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data where
  asymptoticJet : ℕ → ℕ → ℚ
  coefficientExtractor : ℕ → ℕ → ℚ
  bernoulliCoeff : ℕ → ℚ
  evenZetaValue : ℕ → ℚ
  zetaPrefactor : ℕ → ℚ
  coefficientExtractor_correct :
    ∀ R n, n ≤ 2 * R → coefficientExtractor R n = bernoulliCoeff n
  bernoulli_zeta :
    ∀ r, 1 ≤ r → evenZetaValue (2 * r) = zetaPrefactor r * bernoulliCoeff (2 * r)

namespace xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data

/-- The finite-stage Bernoulli coefficient recovered from the jet. -/
def recoveredBernoulli
    (D : xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data) (R r : ℕ) : ℚ :=
  D.coefficientExtractor R (2 * r)

/-- The even-zeta value reconstructed from the recovered Bernoulli coefficient. -/
def recoveredEvenZeta
    (D : xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data) (R r : ℕ) : ℚ :=
  D.zetaPrefactor r * D.recoveredBernoulli R r

/-- Up to stage `R`, the jet determines all Bernoulli coefficients of even index `2r`. -/
def jetDeterminesBernoulli
    (D : xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data) (R : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ R → D.recoveredBernoulli R r = D.bernoulliCoeff (2 * r)

/-- Up to stage `R`, the same recovered coefficients determine the even zeta values. -/
def jetDeterminesEvenZeta
    (D : xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data) (R : ℕ) : Prop :=
  ∀ r, 1 ≤ r → r ≤ R → D.recoveredEvenZeta R r = D.evenZetaValue (2 * r)

end xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data

/-- Paper label: `thm:xi-time-part63b-logcm-phiadic-jet-determines-even-zeta`. -/
theorem paper_xi_time_part63b_logcm_phiadic_jet_determines_even_zeta
    (D : xi_time_part63b_logcm_phiadic_jet_determines_even_zeta_data) :
    ∀ R : Nat, 1 ≤ R → D.jetDeterminesBernoulli R ∧ D.jetDeterminesEvenZeta R := by
  intro R _hR
  constructor
  · intro r _hr hrR
    exact D.coefficientExtractor_correct R (2 * r) (Nat.mul_le_mul_left 2 hrR)
  · intro r hr hrR
    have hcoeff :
        D.coefficientExtractor R (2 * r) = D.bernoulliCoeff (2 * r) :=
      D.coefficientExtractor_correct R (2 * r) (Nat.mul_le_mul_left 2 hrR)
    calc
      D.recoveredEvenZeta R r =
          D.zetaPrefactor r * D.coefficientExtractor R (2 * r) := by
            rfl
      _ = D.zetaPrefactor r * D.bernoulliCoeff (2 * r) := by
            rw [hcoeff]
      _ = D.evenZetaValue (2 * r) := by
            exact (D.bernoulli_zeta r hr).symm

end Omega.Zeta
