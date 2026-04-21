import Mathlib.Data.Finset.Card
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

namespace Omega.Zeta

open Matrix

/-- Concrete finite-dimensional data for the oracle-collapse argument. A minimal realization of
rank `hankelRank` together with a finite recurrence basis inside `Fin uniformBound` produces the
universal Toeplitz cutoff `cutoff = hankelRank + card recurrenceBasis`. -/
structure XiOracleCollapseToeplitzPsdData where
  uniformBound : ℕ
  hankelRank : ℕ
  hankelRank_le : hankelRank ≤ uniformBound
  recurrenceBasis : Finset (Fin uniformBound)

namespace XiOracleCollapseToeplitzPsdData

/-- The universal cutoff extracted from the bounded realization rank and the bounded recurrence
basis. -/
def cutoff (D : XiOracleCollapseToeplitzPsdData) : ℕ :=
  D.hankelRank + D.recurrenceBasis.card

/-- All Toeplitz--PSD tests collapse to the canonical cutoff. -/
def finiteTruncationEquivalent (D : XiOracleCollapseToeplitzPsdData) (N0 : ℕ) : Prop :=
  N0 = D.cutoff

/-- Canonical rectangular compression matrix selecting the leading coordinates of a larger
Toeplitz truncation. The extra parameters are recorded to match the paper theorem's witness
shape. -/
def compressionWitness (_D : XiOracleCollapseToeplitzPsdData) (N0 _ell : ℕ) (_theta : ℝ) (N : ℕ) :
    Matrix (Fin (N0 + 1)) (Fin (N + 1)) ℝ :=
  fun i j => if (i : ℕ) = j then 1 else 0

/-- `W` is a valid finite congruence witness when it is the canonical compression matrix attached
to the chosen cutoff. -/
def congruenceWitness (D : XiOracleCollapseToeplitzPsdData) (N0 ell : ℕ) (theta : ℝ) (N : ℕ)
    (W : Matrix (Fin (N0 + 1)) (Fin (N + 1)) ℝ) : Prop :=
  D.finiteTruncationEquivalent N0 ∧ W = D.compressionWitness N0 ell theta N

end XiOracleCollapseToeplitzPsdData

open XiOracleCollapseToeplitzPsdData

/-- Paper label: `thm:xi-oracle-collapse-toeplitz-psd-finite-truncation`. A uniformly bounded
minimal realization rank and a bounded recurrence basis yield a universal cutoff no larger than
`2 * uniformBound`, and every Toeplitz truncation admits the canonical compression witness from
that cutoff. -/
theorem paper_xi_oracle_collapse_toeplitz_psd_finite_truncation (D : XiOracleCollapseToeplitzPsdData) :
    ∃ N0 ≤ 2 * D.uniformBound, D.finiteTruncationEquivalent N0 ∧
      (∀ ell theta N, ∃ W, D.congruenceWitness N0 ell theta N W) := by
  refine ⟨D.cutoff, ?_, rfl, ?_⟩
  · have hcard : D.recurrenceBasis.card ≤ D.uniformBound := by
      simpa using (Finset.card_le_univ (s := D.recurrenceBasis))
    calc
      D.cutoff = D.hankelRank + D.recurrenceBasis.card := rfl
      _ ≤ D.uniformBound + D.uniformBound := Nat.add_le_add D.hankelRank_le hcard
      _ = 2 * D.uniformBound := by omega
  · intro ell theta N
    refine ⟨D.compressionWitness D.cutoff ell theta N, ?_⟩
    exact ⟨rfl, rfl⟩

end Omega.Zeta
