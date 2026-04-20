import Mathlib
import Omega.Zeta.LucasBarrier

namespace Omega.Zeta

open scoped BigOperators
open Omega.Zeta.LucasBarrier

/-- The Lucas trace `L_m`, regarded in `ℚ` for the fixed-`m` generating functions. -/
def xiTerminalReplicaSoftcoreLucas (m : ℕ) : ℚ :=
  lucas m

/-- The Lucas/Pell exceptional correction term `Ω_m(q)` modeled by its two-step recurrence. -/
def xiTerminalReplicaSoftcoreOmega (m : ℕ) : ℕ → ℚ
  | 0 => 1
  | 1 => xiTerminalReplicaSoftcoreLucas m
  | q + 2 =>
      xiTerminalReplicaSoftcoreLucas m * xiTerminalReplicaSoftcoreOmega m (q + 1) -
        ((-1 : ℚ) ^ m) * xiTerminalReplicaSoftcoreOmega m q

/-- The finite partition contribution to `Tr((T^(q))^m)`. -/
def xiTerminalReplicaSoftcorePartitionTraceCoeff {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) (q : ℕ) : ℚ :=
  ((xiTerminalReplicaSoftcoreLucas m) ^ q + ∑ i, c i * (Theta i) ^ q) / (2 : ℚ) ^ m

/-- The exceptional partition contribution to `S_m(q)`. -/
def xiTerminalReplicaSoftcorePartitionExceptionalCoeff {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) (q : ℕ) : ℚ :=
  (xiTerminalReplicaSoftcoreOmega m q + ∑ i, c i * (Theta i) ^ q) / (2 : ℚ) ^ m

/-- Rational kernel for the Lucas/Pell exceptional channel. -/
def xiTerminalReplicaSoftcoreExceptionalKernel (m : ℕ) (z : ℚ) : ℚ :=
  1 / (1 - xiTerminalReplicaSoftcoreLucas m * z + ((-1 : ℚ) ^ m) * z ^ (2 : ℕ))

/-- Rational `q`-direction generating function for the trace moments. -/
def xiTerminalReplicaSoftcoreTraceGF {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) (z : ℚ) : ℚ :=
  (1 / (1 - xiTerminalReplicaSoftcoreLucas m * z) + ∑ i, c i / (1 - Theta i * z)) /
    (2 : ℚ) ^ m

/-- Rational `q`-direction generating function for the exceptional power sums. -/
def xiTerminalReplicaSoftcoreExceptionalGF {ι : Type*} [Fintype ι]
    (m : ℕ) (c Theta : ι → ℚ) (z : ℚ) : ℚ :=
  (xiTerminalReplicaSoftcoreExceptionalKernel m z + ∑ i, c i / (1 - Theta i * z)) /
    (2 : ℚ) ^ m

/-- Fixed-`m` package for the partition formulas and their rational `q`-direction generating
functions: the trace channel is a sum of geometric kernels, while the exceptional channel replaces
the Lucas term by the Lucas/Pell kernel `1 / (1 - L_m z + (-1)^m z^2)`.
    thm:xi-terminal-replica-softcore-q-genfunc-rational-partition -/
theorem paper_xi_terminal_replica_softcore_q_genfunc_rational_partition
    {ι : Type*} [Fintype ι] (m : ℕ) (c Theta : ι → ℚ) :
    (∀ q, xiTerminalReplicaSoftcorePartitionTraceCoeff m c Theta q =
      ((xiTerminalReplicaSoftcoreLucas m) ^ q + ∑ i, c i * (Theta i) ^ q) / (2 : ℚ) ^ m) ∧
    (∀ q, xiTerminalReplicaSoftcorePartitionExceptionalCoeff m c Theta q =
      (xiTerminalReplicaSoftcoreOmega m q + ∑ i, c i * (Theta i) ^ q) / (2 : ℚ) ^ m) ∧
    xiTerminalReplicaSoftcoreOmega m 0 = 1 ∧
    xiTerminalReplicaSoftcoreOmega m 1 = xiTerminalReplicaSoftcoreLucas m ∧
    (∀ q, xiTerminalReplicaSoftcoreOmega m (q + 2) =
      xiTerminalReplicaSoftcoreLucas m * xiTerminalReplicaSoftcoreOmega m (q + 1) -
        ((-1 : ℚ) ^ m) * xiTerminalReplicaSoftcoreOmega m q) ∧
    (∀ z : ℚ,
      1 - xiTerminalReplicaSoftcoreLucas m * z + ((-1 : ℚ) ^ m) * z ^ (2 : ℕ) ≠ 0 →
      (1 - xiTerminalReplicaSoftcoreLucas m * z + ((-1 : ℚ) ^ m) * z ^ (2 : ℕ)) *
          xiTerminalReplicaSoftcoreExceptionalKernel m z = 1) ∧
    (∀ z : ℚ, xiTerminalReplicaSoftcoreTraceGF m c Theta z =
      (1 / (1 - xiTerminalReplicaSoftcoreLucas m * z) + ∑ i, c i / (1 - Theta i * z)) /
        (2 : ℚ) ^ m) ∧
    (∀ z : ℚ, xiTerminalReplicaSoftcoreExceptionalGF m c Theta z =
      (xiTerminalReplicaSoftcoreExceptionalKernel m z + ∑ i, c i / (1 - Theta i * z)) /
        (2 : ℚ) ^ m) := by
  refine ⟨?_, ?_, rfl, rfl, ?_, ?_, ?_, ?_⟩
  · intro q
    rfl
  · intro q
    rfl
  · intro q
    rfl
  · intro z hz
    unfold xiTerminalReplicaSoftcoreExceptionalKernel
    simpa [one_div] using mul_inv_cancel₀ hz
  · intro z
    rfl
  · intro z
    rfl

end Omega.Zeta
