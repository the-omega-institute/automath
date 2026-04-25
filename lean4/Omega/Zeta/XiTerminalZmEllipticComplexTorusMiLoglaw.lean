import Omega.Zeta.XiTerminalZmCdimBidirectionalMiLoglaw
import Mathlib.Tactic

namespace Omega.Zeta

/-- Concrete uniformization package for transporting the terminal `ξ` process on the complex
points of an elliptic curve to a two-dimensional Kronecker system. -/
structure XiTerminalZmEllipticComplexTorusMiLoglawData where
  entropy : ℕ → ℝ
  mutualInformation : ℕ → ℝ
  wordConst : ℝ
  massConst : ℝ
  ellipticComplexDimension : ℕ
  kroneckerDimension : ℕ
  uniformization_dimension :
    ellipticComplexDimension = 2
  kronecker_transport :
    kroneckerDimension = ellipticComplexDimension
  hentropyLower :
    ∀ n : ℕ, 1 ≤ n →
      (kroneckerDimension : ℝ) * Real.log n - Real.log massConst ≤ entropy n
  hentropyUpper :
    ∀ n : ℕ, 1 ≤ n →
      entropy n ≤ (kroneckerDimension : ℝ) * Real.log n + Real.log wordConst
  hchain :
    ∀ n : ℕ, 1 ≤ n →
      mutualInformation n = 2 * entropy n - entropy (2 * n)

namespace XiTerminalZmEllipticComplexTorusMiLoglawData

/-- Entropy log-law on the analytically uniformized elliptic two-torus. -/
def entropy_loglaw (D : XiTerminalZmEllipticComplexTorusMiLoglawData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    xi_terminal_zm_cdim_bidirectional_mi_loglaw_entropy_window 2 D.massConst D.wordConst n

/-- Mutual-information log-law on the same transported Kronecker system. -/
def mutual_information_loglaw (D : XiTerminalZmEllipticComplexTorusMiLoglawData) : Prop :=
  ∀ n : ℕ, 1 ≤ n →
    xi_terminal_zm_cdim_bidirectional_mi_loglaw_mutual_information_window
      2 D.massConst D.wordConst n D.mutualInformation

end XiTerminalZmEllipticComplexTorusMiLoglawData

open XiTerminalZmEllipticComplexTorusMiLoglawData

/-- Paper label: `cor:xi-terminal-zm-elliptic-complex-torus-mi-loglaw`. Analytic uniformization
identifies `E(ℂ)` with a complex two-torus, the symbolic process transports to a two-dimensional
Kronecker system, and the bidirectional MI log-law is then the `d = 2` case of the existing
cdim theorem. -/
theorem paper_xi_terminal_zm_elliptic_complex_torus_mi_loglaw
    (D : XiTerminalZmEllipticComplexTorusMiLoglawData) :
    D.entropy_loglaw ∧ D.mutual_information_loglaw := by
  have hdim : D.kroneckerDimension = 2 := by
    rw [D.kronecker_transport, D.uniformization_dimension]
  have hbase :=
    paper_xi_terminal_zm_cdim_bidirectional_mi_loglaw
      D.kroneckerDimension D.entropy D.mutualInformation D.wordConst D.massConst
      D.hentropyLower D.hentropyUpper D.hchain
  refine ⟨?_, ?_⟩
  · intro n hn
    have hpair := hbase n hn
    simpa [hdim] using hpair.1
  · intro n hn
    have hpair := hbase n hn
    simpa [hdim] using hpair.2

end Omega.Zeta
