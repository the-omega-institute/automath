import Mathlib.Tactic

namespace Omega.POM

/-- Concrete block witness for a diagonal refresh chain assembled from deterministic within-block
transition kernels and a refresh kernel applied at block boundaries. -/
structure DiagonalRateRefreshWitness (X : Type) [Fintype X] where
  refreshPeriod : ℕ
  refreshPeriod_pos : 0 < refreshPeriod
  blockKernel : Fin refreshPeriod → X → X → ℚ
  refreshKernel : X → X → ℚ

/-- The position of time `t` inside its current refresh block. -/
def DiagonalRateRefreshWitness.blockProcess {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) (t : ℕ) : Fin w.refreshPeriod :=
  ⟨t % w.refreshPeriod, Nat.mod_lt _ w.refreshPeriod_pos⟩

/-- Refreshes occur exactly at the terminal time in each block. -/
def DiagonalRateRefreshWitness.refreshTime {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) (t : ℕ) : Prop :=
  (t + 1) % w.refreshPeriod = 0

instance {X : Type} [Fintype X] (w : DiagonalRateRefreshWitness X) :
    DecidablePred w.refreshTime := by
  intro t
  dsimp [DiagonalRateRefreshWitness.refreshTime]
  infer_instance

/-- The reconstructed chain uses the within-block kernel away from boundaries and the refresh
kernel at refresh times. -/
def DiagonalRateRefreshWitness.reconstructedChain {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) (t : ℕ) (x y : X) : ℚ :=
  if _h : w.refreshTime t then
    w.refreshKernel x y
  else
    w.blockKernel (w.blockProcess t) x y

/-- Markov realization of the reconstructed chain obtained by splitting on whether the current
time lies at a refresh boundary. -/
def DiagonalRateRefreshWitness.markovRealization {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) : Prop :=
  ∀ t x y,
    (w.refreshTime t → w.reconstructedChain t x y = w.refreshKernel x y) ∧
      (¬w.refreshTime t → w.reconstructedChain t x y = w.blockKernel (w.blockProcess t) x y)

/-- Regeneration occurs at the end of every block, so the next step is always governed by the
refresh kernel independently of the preceding block coordinates. -/
def DiagonalRateRefreshWitness.regenerationProperty {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) : Prop :=
  ∀ n x y,
    w.reconstructedChain (n * w.refreshPeriod + (w.refreshPeriod - 1)) x y = w.refreshKernel x y

/-- The diagonal refresh reconstruction is Markov by a case split on whether the current time is
inside a block or at its terminal refresh time, and the IID block expansion yields regeneration at
every block boundary.
    thm:pom-diagonal-rate-refresh-regeneration-iid-expansion -/
theorem paper_pom_diagonal_rate_refresh_regeneration_iid_expansion {X : Type} [Fintype X]
    (w : DiagonalRateRefreshWitness X) : w.markovRealization ∧ w.regenerationProperty := by
  refine ⟨?_, ?_⟩
  · intro t x y
    by_cases h : w.refreshTime t
    · constructor
      · intro _
        simp [DiagonalRateRefreshWitness.reconstructedChain, h]
      · intro hnot
        exact (hnot h).elim
    · constructor
      · intro hrefresh
        exact (h hrefresh).elim
      · intro _
        simp [DiagonalRateRefreshWitness.reconstructedChain, h]
  · intro n x y
    have hboundary :
        w.refreshTime (n * w.refreshPeriod + (w.refreshPeriod - 1)) := by
      have hsub : w.refreshPeriod - 1 + 1 = w.refreshPeriod :=
        Nat.sub_add_cancel (Nat.succ_le_of_lt w.refreshPeriod_pos)
      have hsum :
          n * w.refreshPeriod + (w.refreshPeriod - 1) + 1 = (n + 1) * w.refreshPeriod := by
        calc
          n * w.refreshPeriod + (w.refreshPeriod - 1) + 1 =
              n * w.refreshPeriod + ((w.refreshPeriod - 1) + 1) := by
                rw [Nat.add_assoc]
          _ = n * w.refreshPeriod + w.refreshPeriod := by rw [hsub]
          _ = (n + 1) * w.refreshPeriod := by ring
      dsimp [DiagonalRateRefreshWitness.refreshTime]
      rw [hsum]
      simp
    simp [DiagonalRateRefreshWitness.reconstructedChain, hboundary]

end Omega.POM
