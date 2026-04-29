import Omega.Zeta.XiTerminalZmS3EndoscopicPointcountLocalzetaSquare

namespace Omega.Zeta

/-- Paper label: `cor:xi-terminal-zm-s3-closure-hasse-weil-factorization`. The closure
Hasse--Weil factorization is the paper-facing repackaging of the endoscopic trace split and the
corresponding squared local-zeta numerator factorization. -/
theorem paper_xi_terminal_zm_s3_closure_hasse_weil_factorization
    (p : ℤ) (traceC6 traceC traceR : ℕ → ℤ) (PC6 PC PR : Polynomial ℤ)
    (htrace : ∀ n : ℕ, traceC6 n = traceC n + 2 * traceR n)
    (hpoly : PC6 = PC * PR ^ 2) :
    xiTerminalPointcountIdentity p traceC6 traceC traceR ∧
      xiTerminalLocalZetaSquareFactorization PC6 PC PR := by
  exact paper_xi_terminal_zm_s3_endoscopic_pointcount_localzeta_square
    p traceC6 traceC traceR PC6 PC PR htrace hpoly

end Omega.Zeta
