import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- Terminal signs for the threshold-hitting endpoint. -/
inductive TerminalSign
  | pos
  | neg
  deriving DecidableEq, Fintype

/-- The Bernoulli mass of the terminal sign with success parameter `π`. -/
def terminalSignMass (π : ℝ) : TerminalSign → ℝ
  | .pos => π
  | .neg => 1 - π

/-- A finite-horizon joint generating series for the threshold-hitting time and terminal sign. -/
def tauTerminalSeries (joint : ℕ → TerminalSign → ℝ) (N : ℕ) (u wPos wNeg : ℝ) : ℝ :=
  Finset.sum (Finset.range N) fun n => u ^ n * (joint n TerminalSign.pos * wPos +
    joint n TerminalSign.neg * wNeg)

/-- The finite-horizon generating series of the hitting-time marginal. -/
def tauSeries (tauMass : ℕ → ℝ) (N : ℕ) (u : ℝ) : ℝ :=
  Finset.sum (Finset.range N) fun n => u ^ n * tauMass n

/-- Independence means that each joint mass factors into the time marginal and a fixed sign law. -/
def tauTerminalIndependent (joint : ℕ → TerminalSign → ℝ) (tauMass : ℕ → ℝ) (π : ℝ) : Prop :=
  ∀ n s, joint n s = tauMass n * terminalSignMass π s

/-- Paper-facing wrapper for the constant-ratio law at the terminal threshold sign.
    A fixed ratio `φ^T` between the `+T` and `-T` endpoint masses, together with the time
    marginal, forces the terminal sign to be independent of the hitting time and yields the
    corresponding finite-horizon generating-series factorization.
    prop:pom-tau-terminal-sign-independence -/
theorem paper_pom_tau_terminal_sign_independence
    (phi π : ℝ) (T : ℕ) (joint : ℕ → TerminalSign → ℝ) (tauMass : ℕ → ℝ)
    (hPhi : 0 < phi) (hRatio : ∀ n, joint n TerminalSign.pos = phi ^ T * joint n TerminalSign.neg)
    (hTau : ∀ n, tauMass n = joint n TerminalSign.pos + joint n TerminalSign.neg)
    (hPi : π = phi ^ T / (1 + phi ^ T)) :
    (∀ n, joint n TerminalSign.pos = π * tauMass n ∧
      joint n TerminalSign.neg = (1 - π) * tauMass n) ∧
      tauTerminalIndependent joint tauMass π ∧
      (∀ N u wPos wNeg,
        tauTerminalSeries joint N u wPos wNeg =
          tauSeries tauMass N u * (π * wPos + (1 - π) * wNeg)) := by
  have hDenom : 1 + phi ^ T ≠ 0 := by
    positivity
  have hPointwise : ∀ n, joint n TerminalSign.pos = π * tauMass n ∧
      joint n TerminalSign.neg = (1 - π) * tauMass n := by
    intro n
    have hTau' : tauMass n = (1 + phi ^ T) * joint n TerminalSign.neg := by
      rw [hTau n, hRatio n]
      ring
    have hOneMinus :
        1 - π = 1 / (1 + phi ^ T) := by
      rw [hPi]
      field_simp [hDenom]
      ring
    constructor
    · rw [hPi, hRatio n, hTau']
      field_simp [hDenom]
    · rw [hOneMinus, hTau']
      field_simp [hDenom]
  refine ⟨hPointwise, ?_, ?_⟩
  · intro n s
    cases s with
    | pos =>
        simpa [terminalSignMass, mul_comm] using (hPointwise n).1
    | neg =>
        simpa [terminalSignMass, mul_comm] using (hPointwise n).2
  · intro N u wPos wNeg
    let c : ℝ := π * wPos + (1 - π) * wNeg
    have hTerm :
        ∀ n,
          u ^ n * (joint n TerminalSign.pos * wPos + joint n TerminalSign.neg * wNeg) =
            (u ^ n * tauMass n) * c := by
      intro n
      rcases hPointwise n with ⟨hPos, hNeg⟩
      rw [hPos, hNeg]
      simp [c]
      ring
    unfold tauTerminalSeries tauSeries
    calc
      Finset.sum (Finset.range N) (fun n =>
          u ^ n * (joint n TerminalSign.pos * wPos + joint n TerminalSign.neg * wNeg)) =
          Finset.sum (Finset.range N) (fun n => (u ^ n * tauMass n) * c) := by
            refine Finset.sum_congr rfl ?_
            intro n hn
            exact hTerm n
      _ = Finset.sum (Finset.range N) (fun n => u ^ n * tauMass n) * c := by
            rw [Finset.sum_mul]
      _ = tauSeries tauMass N u * (π * wPos + (1 - π) * wNeg) := by
            rfl

end Omega.POM
