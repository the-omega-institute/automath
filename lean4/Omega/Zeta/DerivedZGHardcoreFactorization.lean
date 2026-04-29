import Mathlib

namespace Omega.Zeta

noncomputable section

open scoped BigOperators

/-- Concrete finite-support data for the ZG hard-core factorization. The index set is truncated at
`support`, so the Bernoulli and hard-core products stabilize after finitely many coordinates. -/
structure DerivedZGHardcoreFactorizationData where
  σ : ℕ
  sigma_pos : 1 ≤ σ
  prime : ℕ → ℕ
  prime_ge_two : ∀ i : ℕ, 2 ≤ prime i
  support : ℕ

namespace DerivedZGHardcoreFactorizationData

/-- Bernoulli occupation parameter at coordinate `i`; it vanishes past the finite support. -/
def bernoulliWeight (D : DerivedZGHardcoreFactorizationData) (i : ℕ) : ℝ :=
  if i < D.support then 1 / ((D.prime i : ℝ) ^ D.σ + 1) else 0

/-- The local hard-core factor excluding adjacent occupied coordinates. -/
def hardcoreCylinderFactor (D : DerivedZGHardcoreFactorizationData) (i : ℕ) : ℝ :=
  1 - D.bernoulliWeight i * D.bernoulliWeight (i + 1)

/-- Finite truncation of the hard-core cylinder weight. -/
def hardcoreCylinderTrunc (D : DerivedZGHardcoreFactorizationData) (N : ℕ) : ℝ :=
  Finset.prod (Finset.range N) fun i => D.hardcoreCylinderFactor i

/-- Finite Euler factor written in the `1 + p^{-σ}` form. -/
def finiteEulerFactor (D : DerivedZGHardcoreFactorizationData) (N : ℕ) : ℝ :=
  Finset.prod (Finset.range N) fun i => 1 + 1 / (D.prime i : ℝ) ^ D.σ

/-- Finite Euler factor rewritten as the quotient `((p_i^σ + 1) / p_i^σ)`. -/
def finiteZetaQuotient (D : DerivedZGHardcoreFactorizationData) (N : ℕ) : ℝ :=
  Finset.prod (Finset.range N) fun i => ((D.prime i : ℝ) ^ D.σ + 1) / (D.prime i : ℝ) ^ D.σ

/-- Finite truncated ZG Dirichlet factorization: Euler quotient times the hard-core cylinder
weight. -/
def finiteDirichletTrunc (D : DerivedZGHardcoreFactorizationData) (N : ℕ) : ℝ :=
  D.finiteZetaQuotient N * D.hardcoreCylinderTrunc N

/-- The stabilized hard-core limit after the finite support has been exhausted. -/
def hardcoreLimit (D : DerivedZGHardcoreFactorizationData) : ℝ :=
  D.hardcoreCylinderTrunc (D.support + 1)

/-- The stabilized Euler quotient rewrite of `ζ(σ) / ζ(2σ)`. -/
def zetaEulerQuotient (D : DerivedZGHardcoreFactorizationData) : ℝ :=
  D.finiteZetaQuotient (D.support + 1)

/-- The stabilized truncated Dirichlet value. -/
def dirichletValue (D : DerivedZGHardcoreFactorizationData) : ℝ :=
  D.finiteDirichletTrunc (D.support + 1)

/-- The finite-support hard-core factorization law: every truncation factors into the Euler
quotient and the cylinder term, the cylinder term stays in `(0, 1]` and decreases with `N`, the
Euler factors admit the `ζ(σ) / ζ(2σ)` local rewrite, the finite-support sequence stabilizes, and
the stabilized value factors accordingly. -/
def hardcoreFactorizationLaw (D : DerivedZGHardcoreFactorizationData) : Prop :=
  (∀ N : ℕ, D.finiteDirichletTrunc N = D.finiteZetaQuotient N * D.hardcoreCylinderTrunc N) ∧
    (∀ N : ℕ, D.hardcoreCylinderTrunc (N + 1) ≤ D.hardcoreCylinderTrunc N) ∧
      (∀ N : ℕ, 0 < D.hardcoreCylinderTrunc N ∧ D.hardcoreCylinderTrunc N ≤ 1) ∧
        (∀ N : ℕ, D.finiteEulerFactor N = D.finiteZetaQuotient N) ∧
          (∀ N : ℕ, D.support + 1 ≤ N → D.hardcoreCylinderTrunc N = D.hardcoreLimit) ∧
            0 < D.hardcoreLimit ∧
              D.hardcoreLimit ≤ 1 ∧
                D.dirichletValue = D.zetaEulerQuotient * D.hardcoreLimit

lemma bernoulliWeight_nonneg (D : DerivedZGHardcoreFactorizationData) (i : ℕ) :
    0 ≤ D.bernoulliWeight i := by
  by_cases hi : i < D.support
  · simp [bernoulliWeight, hi]
    positivity
  · simp [bernoulliWeight, hi]

lemma bernoulliWeight_le_half (D : DerivedZGHardcoreFactorizationData) (i : ℕ) :
    D.bernoulliWeight i ≤ (1 / 2 : ℝ) := by
  by_cases hi : i < D.support
  · have hprime_one : (1 : ℝ) ≤ D.prime i := by
      exact_mod_cast (le_trans (by omega : 1 ≤ 2) (D.prime_ge_two i))
    have hpow_one : (1 : ℝ) ≤ (D.prime i : ℝ) ^ D.σ := by
      simpa using (one_le_pow₀ hprime_one : (1 : ℝ) ≤ (D.prime i : ℝ) ^ D.σ)
    have hden : (2 : ℝ) ≤ (D.prime i : ℝ) ^ D.σ + 1 := by
      linarith
    have hq :
        1 / ((D.prime i : ℝ) ^ D.σ + 1) ≤ 1 / (2 : ℝ) := by
      have := one_div_le_one_div_of_le (by positivity : (0 : ℝ) < 2) hden
      simpa using this
    simpa [bernoulliWeight, hi, one_div] using hq
  · simp [bernoulliWeight, hi]

lemma bernoulliWeight_eq_zero_of_support_le (D : DerivedZGHardcoreFactorizationData) {i : ℕ}
    (hi : D.support ≤ i) : D.bernoulliWeight i = 0 := by
  simp [bernoulliWeight, not_lt.mpr hi]

lemma hardcoreCylinderFactor_pos (D : DerivedZGHardcoreFactorizationData) (i : ℕ) :
    0 < D.hardcoreCylinderFactor i := by
  have h0 : 0 ≤ D.bernoulliWeight i := D.bernoulliWeight_nonneg i
  have h1 : 0 ≤ D.bernoulliWeight (i + 1) := D.bernoulliWeight_nonneg (i + 1)
  have hle0 : D.bernoulliWeight i ≤ (1 / 2 : ℝ) := D.bernoulliWeight_le_half i
  have hle1 : D.bernoulliWeight (i + 1) ≤ (1 / 2 : ℝ) := D.bernoulliWeight_le_half (i + 1)
  have hmul : D.bernoulliWeight i * D.bernoulliWeight (i + 1) ≤ (1 / 4 : ℝ) := by
    nlinarith
  unfold hardcoreCylinderFactor
  linarith

lemma hardcoreCylinderFactor_le_one (D : DerivedZGHardcoreFactorizationData) (i : ℕ) :
    D.hardcoreCylinderFactor i ≤ 1 := by
  have h0 : 0 ≤ D.bernoulliWeight i := D.bernoulliWeight_nonneg i
  have h1 : 0 ≤ D.bernoulliWeight (i + 1) := D.bernoulliWeight_nonneg (i + 1)
  unfold hardcoreCylinderFactor
  nlinarith

lemma hardcoreCylinderTrunc_pos (D : DerivedZGHardcoreFactorizationData) (N : ℕ) :
    0 < D.hardcoreCylinderTrunc N := by
  unfold hardcoreCylinderTrunc
  refine Finset.prod_pos ?_
  intro i hi
  exact D.hardcoreCylinderFactor_pos i

lemma hardcoreCylinderTrunc_le_one (D : DerivedZGHardcoreFactorizationData) (N : ℕ) :
    D.hardcoreCylinderTrunc N ≤ 1 := by
  unfold hardcoreCylinderTrunc
  refine Finset.prod_le_one ?_ ?_
  · intro i hi
    exact le_of_lt (D.hardcoreCylinderFactor_pos i)
  · intro i hi
    exact D.hardcoreCylinderFactor_le_one i

lemma hardcoreCylinderTrunc_step_le (D : DerivedZGHardcoreFactorizationData) (N : ℕ) :
    D.hardcoreCylinderTrunc (N + 1) ≤ D.hardcoreCylinderTrunc N := by
  rw [hardcoreCylinderTrunc, Finset.prod_range_succ]
  have hmul :=
    mul_le_mul_of_nonneg_left (D.hardcoreCylinderFactor_le_one N)
      (le_of_lt (D.hardcoreCylinderTrunc_pos N))
  simpa [one_mul] using hmul

lemma finiteEulerFactor_eq_finiteZetaQuotient (D : DerivedZGHardcoreFactorizationData) (N : ℕ) :
    D.finiteEulerFactor N = D.finiteZetaQuotient N := by
  unfold finiteEulerFactor finiteZetaQuotient
  refine Finset.prod_congr rfl ?_
  intro i hi
  have hprime_ne : (D.prime i : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (lt_of_lt_of_le (by decide : 0 < 2) (D.prime_ge_two i)))
  have hpow_ne : ((D.prime i : ℝ) ^ D.σ) ≠ 0 := pow_ne_zero _ hprime_ne
  field_simp [hpow_ne]

lemma hardcoreCylinderTrunc_stabilizes (D : DerivedZGHardcoreFactorizationData) {N : ℕ}
    (hN : D.support + 1 ≤ N) : D.hardcoreCylinderTrunc N = D.hardcoreLimit := by
  let m := N - (D.support + 1)
  have hNm : N = D.support + 1 + m := by
    dsimp [m]
    omega
  rw [hNm, hardcoreLimit, hardcoreCylinderTrunc, Finset.prod_range_add]
  have htail :
      Finset.prod (Finset.range m) (fun x => D.hardcoreCylinderFactor (D.support + 1 + x)) = 1 := by
    refine Finset.prod_eq_one ?_
    intro x hx
    have hs : D.support ≤ D.support + 1 + x := by omega
    simp [hardcoreCylinderFactor, bernoulliWeight, not_lt.mpr hs]
  simpa [hardcoreCylinderTrunc, htail]

end DerivedZGHardcoreFactorizationData

open DerivedZGHardcoreFactorizationData

/-- Paper label: `thm:derived-zg-hardcore-factorization`.
The finite-support ZG truncations factor as a `ζ(σ) / ζ(2σ)` Euler quotient times a hard-core
cylinder weight. The cylinder weights decrease in `N`, stay in `(0, 1]`, stabilize once the
finite support is exhausted, and the stabilized truncation gives the resulting hard-core
factorization law. -/
theorem paper_derived_zg_hardcore_factorization (D : DerivedZGHardcoreFactorizationData) :
    D.hardcoreFactorizationLaw := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro N
    rfl
  · intro N
    exact D.hardcoreCylinderTrunc_step_le N
  · intro N
    exact ⟨D.hardcoreCylinderTrunc_pos N, D.hardcoreCylinderTrunc_le_one N⟩
  · intro N
    exact D.finiteEulerFactor_eq_finiteZetaQuotient N
  · intro N hN
    exact D.hardcoreCylinderTrunc_stabilizes hN
  · exact D.hardcoreCylinderTrunc_pos (D.support + 1)
  · exact D.hardcoreCylinderTrunc_le_one (D.support + 1)
  · rfl

end

end Omega.Zeta
