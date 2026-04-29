import Mathlib

open scoped BigOperators Topology

namespace Omega.Zeta

noncomputable section

/-- The common moment prefactor in the fold-`π` finite-rank truncation tower. -/
def foldpiMomentPrefactor (k : ℕ) : ℝ :=
  (1 + Real.goldenRatio ^ (2 * k)) /
    (Real.goldenRatio * (4 : ℝ) ^ k * Real.pi ^ (2 * k + 2))

/-- The `n`-th atomic contribution to the `k`-th moment, indexed from `n = 1`. -/
def foldpiMomentTerm (k n : ℕ) : ℝ :=
  foldpiMomentPrefactor k / (n : ℝ) ^ (2 * k + 2)

/-- The truncated `k`-th moment keeping the first `N` atomic pairs. -/
def foldpiTruncatedMoment (k N : ℕ) : ℝ :=
  Finset.sum (Finset.range N) (fun n => foldpiMomentTerm k (n + 1))

/-- The explicit tail after stage `N`. -/
def foldpiTailMoment (k N : ℕ) : ℝ :=
  foldpiMomentPrefactor k * ∑' n : ℕ, 1 / ((N + 1 + n : ℕ) : ℝ) ^ (2 * k + 2)

/-- Concrete data for the full moment sequence that the finite-rank tower exhausts. -/
structure XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData where
  fullMoment : ℕ → ℝ
  fullMoment_tail :
    ∀ k N, fullMoment k = foldpiTruncatedMoment k N + foldpiTailMoment k N

namespace XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData

/-- Closed form, strict increase of the truncations, and the exact tail identity. -/
def finiteRankMomentExhaustion (D : XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData) : Prop :=
  (∀ k N,
      foldpiTruncatedMoment k N =
        foldpiMomentPrefactor k *
          Finset.sum (Finset.range N) (fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2))) ∧
    (∀ k, 0 < foldpiTruncatedMoment k 1) ∧
    (∀ k N, foldpiTruncatedMoment k N < foldpiTruncatedMoment k (N + 1)) ∧
    (∀ k N, D.fullMoment k - foldpiTruncatedMoment k N = foldpiTailMoment k N)

end XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData

open XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData

private lemma foldpiMomentPrefactor_pos (k : ℕ) : 0 < foldpiMomentPrefactor k := by
  have hphi : 0 < Real.goldenRatio := Real.goldenRatio_pos
  unfold foldpiMomentPrefactor
  positivity

private lemma foldpiMomentTerm_pos (k n : ℕ) (hn : 1 ≤ n) : 0 < foldpiMomentTerm k n := by
  unfold foldpiMomentTerm
  have hden : 0 < (n : ℝ) ^ (2 * k + 2) := by positivity
  exact div_pos (foldpiMomentPrefactor_pos k) hden

private lemma foldpiTruncatedMoment_eq_closed (k N : ℕ) :
    foldpiTruncatedMoment k N =
      foldpiMomentPrefactor k *
        Finset.sum (Finset.range N) (fun n => 1 / ((n + 1 : ℕ) : ℝ) ^ (2 * k + 2)) := by
  unfold foldpiTruncatedMoment foldpiMomentTerm
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro n hn
  ring

private lemma foldpiTruncatedMoment_succ (k N : ℕ) :
    foldpiTruncatedMoment k (N + 1) = foldpiTruncatedMoment k N + foldpiMomentTerm k (N + 1) := by
  rw [foldpiTruncatedMoment, foldpiTruncatedMoment, Finset.sum_range_succ]

/-- Paper label: `thm:xi-time-part9zbg-foldpi-finite-rank-moment-exhaustion`. -/
theorem paper_xi_time_part9zbg_foldpi_finite_rank_moment_exhaustion
    (D : XiTimePart9zbgFoldpiFiniteRankMomentExhaustionData) : D.finiteRankMomentExhaustion := by
  refine ⟨foldpiTruncatedMoment_eq_closed, ?_, ?_, ?_⟩
  · intro k
    rw [show (1 : ℕ) = 0 + 1 by norm_num, foldpiTruncatedMoment_succ]
    have h0 : foldpiTruncatedMoment k 0 = 0 := by
      simp [foldpiTruncatedMoment]
    rw [h0]
    simpa using foldpiMomentTerm_pos k 1 (by omega)
  · intro k N
    rw [foldpiTruncatedMoment_succ]
    have hpos : 0 < foldpiMomentTerm k (N + 1) := foldpiMomentTerm_pos k (N + 1) (by omega)
    linarith
  · intro k N
    have htail := D.fullMoment_tail k N
    linarith

end

end Omega.Zeta
