import Mathlib.Tactic

namespace Omega.POM

/-- Concrete witness packaging the IID block data, holding times, within-block kernel, and
boundary refresh kernel for a diagonal refresh renewal coding model. -/
structure pom_diagonal_rate_refresh_renewal_coding_witness (X : Type) [Fintype X] where
  refresh_period : ℕ
  refresh_period_pos : 0 < refresh_period
  iid_block_data : ℕ → Fin refresh_period → X
  holding_time : ℕ → ℕ
  holding_time_eq : ∀ n, holding_time n = refresh_period
  block_kernel : Fin refresh_period → X → X → ℚ
  refresh_kernel : X → X → ℚ

/-- Time `t` viewed inside its current refresh block. -/
def pom_diagonal_rate_refresh_renewal_coding_block_position {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) (t : ℕ) : Fin w.refresh_period :=
  ⟨t % w.refresh_period, Nat.mod_lt _ w.refresh_period_pos⟩

/-- The deterministic block expansion read from the witness. -/
def pom_diagonal_rate_refresh_renewal_coding_block_expansion {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) (n : ℕ) :
    Fin w.refresh_period → X :=
  w.iid_block_data n

/-- A time is terminal exactly when it ends the current block. -/
def pom_diagonal_rate_refresh_renewal_coding_block_terminal {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) (t : ℕ) : Prop :=
  (t + 1) % w.refresh_period = 0

instance {X : Type} [Fintype X] (w : pom_diagonal_rate_refresh_renewal_coding_witness X) :
    DecidablePred (pom_diagonal_rate_refresh_renewal_coding_block_terminal w) := by
  intro t
  dsimp [pom_diagonal_rate_refresh_renewal_coding_block_terminal]
  infer_instance

/-- The reconstructed one-step kernel uses the refresh kernel exactly at block boundaries and the
within-block kernel otherwise. -/
def pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) (t : ℕ) (x y : X) : ℚ :=
  if pom_diagonal_rate_refresh_renewal_coding_block_terminal w t then
    w.refresh_kernel x y
  else
    w.block_kernel (pom_diagonal_rate_refresh_renewal_coding_block_position w t) x y

/-- The block expansion is literally the packaged IID block data. -/
def pom_diagonal_rate_refresh_renewal_coding_iid_block_expansion {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) : Prop :=
  ∀ n, pom_diagonal_rate_refresh_renewal_coding_block_expansion w n = w.iid_block_data n

/-- One-step kernel description obtained by splitting on whether the current block ends. -/
def pom_diagonal_rate_refresh_renewal_coding_one_step_kernel {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) : Prop :=
  ∀ t x y,
    (pom_diagonal_rate_refresh_renewal_coding_block_terminal w t →
        pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain w t x y =
          w.refresh_kernel x y) ∧
      (¬pom_diagonal_rate_refresh_renewal_coding_block_terminal w t →
        pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain w t x y =
          w.block_kernel (pom_diagonal_rate_refresh_renewal_coding_block_position w t) x y)

/-- Regeneration occurs at the terminal time of each refresh block. -/
def pom_diagonal_rate_refresh_renewal_coding_regeneration {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) : Prop :=
  ∀ n x y,
    pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain w
        (n * w.refresh_period + (w.refresh_period - 1)) x y =
      w.refresh_kernel x y

/-- The IID block expansion yields equal holding times and therefore equally spaced refresh times. -/
def pom_diagonal_rate_refresh_renewal_coding_iid_refresh_times {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) : Prop :=
  ∀ n,
    w.holding_time n = w.refresh_period ∧
      pom_diagonal_rate_refresh_renewal_coding_block_terminal w
        (n * w.refresh_period + (w.refresh_period - 1))

/-- Paper-facing package for the renewal coding witness. -/
def pom_diagonal_rate_refresh_renewal_coding_statement {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) : Prop :=
  pom_diagonal_rate_refresh_renewal_coding_iid_block_expansion w ∧
    pom_diagonal_rate_refresh_renewal_coding_one_step_kernel w ∧
    pom_diagonal_rate_refresh_renewal_coding_regeneration w ∧
    pom_diagonal_rate_refresh_renewal_coding_iid_refresh_times w

lemma pom_diagonal_rate_refresh_renewal_coding_boundary_terminal {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) (n : ℕ) :
    pom_diagonal_rate_refresh_renewal_coding_block_terminal w
      (n * w.refresh_period + (w.refresh_period - 1)) := by
  have hsub : w.refresh_period - 1 + 1 = w.refresh_period :=
    Nat.sub_add_cancel (Nat.succ_le_of_lt w.refresh_period_pos)
  have hsum :
      n * w.refresh_period + (w.refresh_period - 1) + 1 = (n + 1) * w.refresh_period := by
    calc
      n * w.refresh_period + (w.refresh_period - 1) + 1 =
          n * w.refresh_period + ((w.refresh_period - 1) + 1) := by
            rw [Nat.add_assoc]
      _ = n * w.refresh_period + w.refresh_period := by rw [hsub]
      _ = (n + 1) * w.refresh_period := by ring
  dsimp [pom_diagonal_rate_refresh_renewal_coding_block_terminal]
  rw [hsum]
  simp

/-- The reconstructed chain is obtained by the boundary split, regeneration happens at each block
end, and the constant holding-time expansion gives the IID refresh schedule.
    thm:pom-diagonal-rate-refresh-renewal-coding -/
theorem paper_pom_diagonal_rate_refresh_renewal_coding {X : Type} [Fintype X]
    (w : pom_diagonal_rate_refresh_renewal_coding_witness X) :
    pom_diagonal_rate_refresh_renewal_coding_statement w := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro n
    rfl
  · intro t x y
    by_cases h : pom_diagonal_rate_refresh_renewal_coding_block_terminal w t
    · constructor
      · intro _
        simp [pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain, h]
      · intro hnot
        exact (hnot h).elim
    · constructor
      · intro hterminal
        exact (h hterminal).elim
      · intro _
        simp [pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain, h]
  · intro n x y
    have hterminal := pom_diagonal_rate_refresh_renewal_coding_boundary_terminal w n
    simp [pom_diagonal_rate_refresh_renewal_coding_reconstructed_chain, hterminal]
  · intro n
    exact ⟨w.holding_time_eq n, pom_diagonal_rate_refresh_renewal_coding_boundary_terminal w n⟩

end Omega.POM
