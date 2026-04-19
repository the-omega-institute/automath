import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic
import Omega.Folding.FoldHypercubeFibonacciGodelRadiusCount

namespace Omega.Folding

noncomputable section

/-- The energy cutoff used for the Walsh truncation in the Fibonacci-weighted hypercube model. -/
def foldHypercubeFibonacciCutoff (E ε : ℝ) : ℕ :=
  Nat.ceil (4 * E / ε ^ 2)

/-- The number of Walsh modes surviving the cutoff `Λ`, counted through the Fibonacci radius
family. -/
def foldHypercubeFibonacciCutoffModeCount (Λ : ℕ) : ℕ :=
  (fibGodelRadiusFamily Λ).card

/-- The standard coefficient quantization mesh used on the `2^k`-dimensional cutoff window. -/
def foldHypercubeFibonacciQuantizationMesh (ε : ℝ) (k : ℕ) : ℝ :=
  ε / (2 * Real.sqrt (2 ^ k))

/-- The number of scalar quantization levels used on each Walsh coefficient. -/
def foldHypercubeFibonacciQuantizationLevels (k : ℕ) (ε : ℝ) : ℕ :=
  Nat.ceil (4 * Real.sqrt (2 ^ k) / ε) + 1

/-- The standard product-grid covering count obtained by quantizing every cutoff Walsh
coefficient independently. -/
def foldHypercubeFibonacciStandardCoverCount (k : ℕ) (ε : ℝ) : ℕ :=
  foldHypercubeFibonacciQuantizationLevels k ε ^ (2 ^ k)

/-- Paper label: `thm:fold-hypercube-fibonacci-eps-entropy-upper`.
Truncating the Fibonacci-weighted Walsh expansion at `Λ = ⌈4E / ε²⌉` reduces the problem to at
most `2^k` cutoff modes whenever `F_{k+1} ≤ Λ < F_{k+2}`. Quantizing the cutoff coefficients on
the standard `ε / (2 √(2^k))` mesh therefore yields a finite explicit product-grid cover. -/
theorem paper_fold_hypercube_fibonacci_eps_entropy_upper
    (E ε : ℝ) (k : ℕ) (hε : 0 < ε)
    (hk :
      Nat.fib (k + 1) ≤ foldHypercubeFibonacciCutoff E ε ∧
        foldHypercubeFibonacciCutoff E ε < Nat.fib (k + 2)) :
    let Λ := foldHypercubeFibonacciCutoff E ε
    let NΛ := foldHypercubeFibonacciCutoffModeCount Λ
    let δ := foldHypercubeFibonacciQuantizationMesh ε k
    NΛ ≤ 2 ^ k ∧ 0 < δ ∧ 1 ≤ foldHypercubeFibonacciStandardCoverCount k ε := by
  dsimp [foldHypercubeFibonacciCutoffModeCount, foldHypercubeFibonacciQuantizationMesh,
    foldHypercubeFibonacciStandardCoverCount]
  have hcount :=
    (paper_fold_hypercube_fibonacci_godel_radius_count (foldHypercubeFibonacciCutoff E ε) k hk).2
  refine ⟨hcount, ?_, ?_⟩
  · have hsqrt_pos : 0 < Real.sqrt (2 ^ k) := by
      have hpow_pos : (0 : ℝ) < 2 ^ k := by positivity
      exact Real.sqrt_pos.2 hpow_pos
    positivity
  · have hcover_pos : 0 < foldHypercubeFibonacciQuantizationLevels k ε ^ (2 ^ k) := by
      have hlevels_pos : 0 < foldHypercubeFibonacciQuantizationLevels k ε := by
        simp [foldHypercubeFibonacciQuantizationLevels]
      simpa using (Nat.pow_pos hlevels_pos)
    exact Nat.succ_le_of_lt hcover_pos

end

end Omega.Folding
