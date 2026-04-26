import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper theorem:
`prop:xi-cauchy-poisson-sixth-signature-negativity-rigidity` -/
theorem paper_xi_cauchy_poisson_sixth_signature_negativity_rigidity
    (σ μ3 μ4 : ℝ) (hσ : 0 < σ) (hgram : σ^2 * μ4 - μ3^2 - σ^6 >= 0) :
    let gamma1 := μ3 / σ^3
    let beta2 := μ4 / σ^4
    let J := 1 - 8 * beta2 + 6 * gamma1^2
    let C6 := σ^6 * J / 64
    J <= -7 - 2 * gamma1^2 ∧
      C6 <= -(μ3^2) / 32 - 7 * σ^6 / 64 ∧
      (C6 = -(7 * σ^6) / 64 -> μ3 = 0 ∧ μ4 = σ^4) := by
  dsimp
  let gamma1 : ℝ := μ3 / σ ^ 3
  let beta2 : ℝ := μ4 / σ ^ 4
  let J : ℝ := 1 - 8 * beta2 + 6 * gamma1 ^ 2
  let C6 : ℝ := σ ^ 6 * J / 64
  change J <= -7 - 2 * gamma1 ^ 2 ∧
      C6 <= -(μ3 ^ 2) / 32 - 7 * σ ^ 6 / 64 ∧
      (C6 = -(7 * σ ^ 6) / 64 -> μ3 = 0 ∧ μ4 = σ ^ 4)
  have hσ0 : σ ≠ 0 := ne_of_gt hσ
  have hsix : 0 < σ ^ 6 := by positivity
  have hγrel : gamma1 * σ ^ 3 = μ3 := by
    dsimp [gamma1]
    field_simp [hσ0]
  have hβrel : beta2 * σ ^ 4 = μ4 := by
    dsimp [beta2]
    field_simp [hσ0]
  have hγsq : gamma1 ^ 2 * σ ^ 6 = μ3 ^ 2 := by
    have hsq := congrArg (fun x : ℝ => x ^ 2) hγrel
    nlinarith [hsq]
  have hβσ6 : beta2 * σ ^ 6 = σ ^ 2 * μ4 := by
    nlinarith [hβrel]
  have hC6rel : 64 * C6 = σ ^ 6 * J := by
    dsimp [C6]
    ring
  have hβlb : gamma1 ^ 2 + 1 ≤ beta2 := by
    have hmul : (gamma1 ^ 2 + 1) * σ ^ 6 ≤ beta2 * σ ^ 6 := by
      nlinarith [hgram, hγsq, hβσ6]
    by_contra hlt
    have hlt' : beta2 * σ ^ 6 < (gamma1 ^ 2 + 1) * σ ^ 6 := by
      nlinarith [hlt, hsix]
    linarith
  have hJbound : J <= -7 - 2 * gamma1 ^ 2 := by
    dsimp [J]
    nlinarith
  have hC6bound : C6 <= -(μ3 ^ 2) / 32 - 7 * σ ^ 6 / 64 := by
    have hmul : 64 * C6 ≤ -2 * μ3 ^ 2 - 7 * σ ^ 6 := by
      nlinarith [hJbound, hγsq, hC6rel]
    nlinarith [hmul]
  refine ⟨hJbound, hC6bound, ?_⟩
  intro hEq
  have hJeq : J = -7 := by
    have hmul : σ ^ 6 * J = -7 * σ ^ 6 := by
      nlinarith [hEq, hC6rel]
    nlinarith [hmul, hσ]
  have hγsq_zero : gamma1 ^ 2 = 0 := by
    nlinarith [hJbound, hJeq]
  have hγzero : gamma1 = 0 := by
    nlinarith [sq_nonneg gamma1, hγsq_zero]
  have hμ3 : μ3 = 0 := by
    calc
      μ3 = gamma1 * σ ^ 3 := by simpa using hγrel.symm
      _ = 0 := by simp [hγzero]
  have hβeq : beta2 = 1 := by
    dsimp [J] at hJeq
    nlinarith [hJeq, hγsq_zero]
  have hμ4 : μ4 = σ ^ 4 := by
    calc
      μ4 = beta2 * σ ^ 4 := by simpa using hβrel.symm
      _ = σ ^ 4 := by simp [hβeq]
  exact ⟨hμ3, hμ4⟩

end Omega.Zeta
