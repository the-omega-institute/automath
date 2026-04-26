import Mathlib.Data.Finset.Card
import Mathlib.Order.Monotone.Basic
import Mathlib.Order.OrderIsoNat

namespace Omega.Zeta

/-- Finite kernel-chain model for the terminal GBC anomaly-coordinate count. The decreasing finite
sets model the stabilized dual-kernel coordinates of the visible strictification quotients. -/
structure xi_terminal_gbc_anomaly_coordinate_count_Data where
  α : Type*
  xi_terminal_gbc_anomaly_coordinate_count_instFintype : Fintype α
  xi_terminal_gbc_anomaly_coordinate_count_instDecidableEq : DecidableEq α
  xi_terminal_gbc_anomaly_coordinate_count_kernel_chain : ℕ → Finset α
  xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_antitone :
    ∀ m,
      xi_terminal_gbc_anomaly_coordinate_count_kernel_chain (m + 1) ⊆
        xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m

namespace xi_terminal_gbc_anomaly_coordinate_count_Data

/-- The anomaly-coordinate count at stage `m`, identified with the cardinality of the concrete
kernel chain. -/
def xi_terminal_gbc_anomaly_coordinate_count_coordinate_count
    (D : xi_terminal_gbc_anomaly_coordinate_count_Data) (m : ℕ) : ℕ := by
  letI := D.xi_terminal_gbc_anomaly_coordinate_count_instFintype
  letI := D.xi_terminal_gbc_anomaly_coordinate_count_instDecidableEq
  exact (D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m).card

/-- The coordinate count is exactly the kernel cardinality at each stage. -/
def count_formula (D : xi_terminal_gbc_anomaly_coordinate_count_Data) : Prop :=
  ∀ m,
    D.xi_terminal_gbc_anomaly_coordinate_count_coordinate_count m =
      (D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m).card

/-- The stabilized kernel chain is cardinality-monotone. -/
def counts_monotone (D : xi_terminal_gbc_anomaly_coordinate_count_Data) : Prop :=
  ∀ m,
    D.xi_terminal_gbc_anomaly_coordinate_count_coordinate_count (m + 1) ≤
      D.xi_terminal_gbc_anomaly_coordinate_count_coordinate_count m

/-- A descending finite kernel chain is eventually constant, so the corresponding anomaly counts
freeze as well. -/
def eventual_stability (D : xi_terminal_gbc_anomaly_coordinate_count_Data) : Prop :=
  ∃ m0 : ℕ,
    ∀ m ≥ m0,
      D.xi_terminal_gbc_anomaly_coordinate_count_coordinate_count m =
        D.xi_terminal_gbc_anomaly_coordinate_count_coordinate_count m0

private lemma xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_eventual_stability
    (D : xi_terminal_gbc_anomaly_coordinate_count_Data) :
    ∃ m0 : ℕ,
      ∀ m ≥ m0,
        D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m =
          D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m0 := by
  letI := D.xi_terminal_gbc_anomaly_coordinate_count_instFintype
  letI := D.xi_terminal_gbc_anomaly_coordinate_count_instDecidableEq
  let c : ℕ → ℕ := fun m =>
    (D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m).card
  have hcardmono : ∀ m, c (m + 1) ≤ c m := by
    intro m
    exact
      Finset.card_le_card
        (D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_antitone m)
  let chain : ℕ →o OrderDual ℕ :=
    ⟨c, antitone_nat_of_succ_le hcardmono⟩
  obtain ⟨m0, hm0⟩ := WellFoundedGT.monotone_chain_condition chain
  have hanti :
      Antitone D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain :=
    antitone_nat_of_succ_le
      D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_antitone
  refine ⟨m0, ?_⟩
  intro m hm
  have hsubset :
      D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m ⊆
        D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain m0 :=
    hanti hm
  apply Finset.eq_of_subset_of_card_le hsubset
  simpa [c] using (Eq.ge (hm0 m hm))

end xi_terminal_gbc_anomaly_coordinate_count_Data

open xi_terminal_gbc_anomaly_coordinate_count_Data

/-- Paper label: `thm:xi-terminal-gbc-anomaly-coordinate-count`. In the finite terminal
strictification model, anomaly coordinates are counted by the concrete dual-kernel chain; the
counts are monotone because the kernels form a descending chain, and eventual constancy follows
from the monotone-chain condition on finite cardinalities. -/
theorem paper_xi_terminal_gbc_anomaly_coordinate_count
    (D : xi_terminal_gbc_anomaly_coordinate_count_Data) :
    D.count_formula ∧ D.counts_monotone ∧ D.eventual_stability := by
  refine ⟨?_, ?_, ?_⟩
  · intro m
    rfl
  · intro m
    letI := D.xi_terminal_gbc_anomaly_coordinate_count_instFintype
    letI := D.xi_terminal_gbc_anomaly_coordinate_count_instDecidableEq
    simpa [xi_terminal_gbc_anomaly_coordinate_count_coordinate_count] using
      Finset.card_le_card
        (D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_antitone m)
  · obtain ⟨m0, hm0⟩ :=
      D.xi_terminal_gbc_anomaly_coordinate_count_kernel_chain_eventual_stability
    refine ⟨m0, ?_⟩
    intro m hm
    have hstable := hm0 m hm
    simpa [xi_terminal_gbc_anomaly_coordinate_count_coordinate_count, hstable]

end Omega.Zeta
