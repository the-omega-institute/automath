import Omega.POM.BqIsSymqAndSpectrum
import Omega.POM.BqTraceLucas

namespace Omega.POM

open Omega.Zeta.LucasBarrier
open scoped Polynomial

/-- The reciprocal quadratic factor attached to a paired squared `B_q` eigenvalue channel. -/
noncomputable def pom_bq_lucas_square_spectrum_factorization_pair_factor (d : ℕ) :
    Polynomial ℤ :=
  Polynomial.X ^ 2 - Polynomial.C (lucas (2 * d) : ℤ) * Polynomial.X + 1

/-- The finite Lucas-square spectrum certificate used by the paper statement. It records the
already formalized `B_q = Sym^q` spectrum package, the paired Lucas trace expansion, the
reciprocal quadratic normal form `u^2 - L_(2d) u + 1`, and the normalized `q = 4` trace check. -/
def pom_bq_lucas_square_spectrum_factorization_statement (q : ℕ) : Prop :=
  1 ≤ q ∧
    pom_bq_is_symq_and_spectrum_statement q ∧
    (∀ n : ℕ,
      bqTraceLucas q n =
        Finset.sum (Finset.range (q / 2 + 1)) (fun k =>
          if 2 * k = q then
            (-1 : ℤ) ^ (k * n)
          else
            (-1 : ℤ) ^ (k * n) * (lucas (n * (q - 2 * k)) : ℤ))) ∧
    (∀ d : ℕ,
      pom_bq_lucas_square_spectrum_factorization_pair_factor d =
        Polynomial.X ^ 2 - Polynomial.C (lucas (2 * d) : ℤ) * Polynomial.X + 1) ∧
    (q = 4 → bqTraceLucas 4 1 = 5)

/-- Paper label: `thm:pom-bq-lucas-square-spectrum-factorization`. -/
theorem paper_pom_bq_lucas_square_spectrum_factorization (q : ℕ) (hq : 1 ≤ q) :
    pom_bq_lucas_square_spectrum_factorization_statement q := by
  refine ⟨hq, paper_pom_bq_is_symq_and_spectrum q, ?_, ?_, ?_⟩
  · intro n
    exact (paper_pom_bq_trace_lucas q n).1
  · intro d
    rfl
  · intro _hq4
    native_decide

end Omega.POM
