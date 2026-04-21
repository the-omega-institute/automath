import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Weil's point-count formula written in terms of the `H¹` Frobenius trace sequence. -/
def xiTerminalPointCountFromTrace (p : ℤ) (frobTrace : ℕ → ℤ) (n : ℕ) : ℤ :=
  p ^ n + 1 - frobTrace n

/-- Point-count identity induced by the endoscopic `H¹(C₆) ≅ H¹(C) ⊕ H¹(R)^{⊕2}` trace split. -/
def xiTerminalPointcountIdentity
    (p : ℤ) (traceC6 traceC traceR : ℕ → ℤ) : Prop :=
  ∀ n : ℕ,
    xiTerminalPointCountFromTrace p traceC6 n =
      xiTerminalPointCountFromTrace p traceC n +
        2 * xiTerminalPointCountFromTrace p traceR n - 2 * (p ^ n + 1)

/-- Local-zeta numerator factorization coming from multiplicativity of Frobenius characteristic
polynomials under the same `H¹` direct-sum decomposition. -/
def xiTerminalLocalZetaSquareFactorization
    (PC6 PC PR : Polynomial ℤ) : Prop :=
  PC6 = PC * PR ^ 2

lemma xiTerminal_pointcount_from_trace_split
    (p : ℤ) (traceC6 traceC traceR : ℕ → ℤ)
    (htrace : ∀ n : ℕ, traceC6 n = traceC n + 2 * traceR n) :
    xiTerminalPointcountIdentity p traceC6 traceC traceR := by
  intro n
  dsimp [xiTerminalPointCountFromTrace]
  rw [htrace n]
  ring

lemma xiTerminal_local_zeta_from_charpoly_split
    (PC6 PC PR : Polynomial ℤ)
    (hpoly : PC6 = PC * PR ^ 2) :
    xiTerminalLocalZetaSquareFactorization PC6 PC PR := by
  exact hpoly

/-- Translate an endoscopic `H¹` trace split into the Weil point-count identity, and use the
matching Frobenius-characteristic-polynomial factorization to obtain the squared local-zeta
numerator factorization.
    cor:xi-terminal-zm-s3-endoscopic-pointcount-localzeta-square -/
theorem paper_xi_terminal_zm_s3_endoscopic_pointcount_localzeta_square
    (p : ℤ)
    (traceC6 traceC traceR : ℕ → ℤ)
    (PC6 PC PR : Polynomial ℤ)
    (htrace : ∀ n : ℕ, traceC6 n = traceC n + 2 * traceR n)
    (hpoly : PC6 = PC * PR ^ 2) :
    xiTerminalPointcountIdentity p traceC6 traceC traceR ∧
      xiTerminalLocalZetaSquareFactorization PC6 PC PR := by
  exact ⟨xiTerminal_pointcount_from_trace_split p traceC6 traceC traceR htrace,
    xiTerminal_local_zeta_from_charpoly_split PC6 PC PR hpoly⟩

end Omega.Zeta
