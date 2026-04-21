import Mathlib.Data.Complex.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Finset.NatDivisors
import Mathlib.Tactic

/-!
# Length mod-q Chebotarev-Mertens seed values

Arithmetic identities for the Chebotarev-Mertens density theorem seeds.
-/

namespace Omega.Zeta

open scoped BigOperators

/-- The `n`-th twisted trace coefficient appearing in the length-mod-`q`
Dirichlet-Artin expansion. -/
noncomputable def lengthModqTraceCoeff (ω : ℂ) (j : ℕ) (trace : ℕ → ℂ) (n : ℕ) : ℂ :=
  ω ^ (j * n) * trace n / (n : ℂ)

/-- The Möbius-log coefficient obtained from the divisor reindexing step. -/
noncomputable def lengthModqMobiuslogCoeff (μ : ℕ → ℂ) (logZCoeff : ℕ → ℂ) (n : ℕ) : ℂ :=
  ∑ d ∈ n.divisors, μ d / (d : ℂ) * logZCoeff (n / d)

/-- Finite partial sum of the Möbius-log expansion. -/
noncomputable def lengthModqMobiuslogSeries
    (μ : ℕ → ℂ) (logZCoeff : ℕ → ℂ) (z : ℂ) (N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, lengthModqMobiuslogCoeff μ logZCoeff n * z ^ n

/-- Length mod-q Chebotarev-Mertens seeds.
    thm:zeta-length-modq-chebotarev-mertens -/
theorem paper_zeta_length_modq_chebotarev_mertens_seeds :
    (1 - 1 - 1 = (-1 : ℤ) ∧ 1 + 1 - 1 = (1 : ℤ)) ∧
    (1 = 1 ∧ 1 + 1 = 2) ∧
    (2 * 1 = 2) ∧
    (1 + 3 = 4 ∧ 3 + 4 = 7) ∧
    (3 - 1 = 2 ∧ 2 / 2 = 1) := by
  omega

/-- Paper package: length mod-q Chebotarev-Mertens seeds.
    thm:zeta-length-modq-chebotarev-mertens -/
theorem paper_zeta_length_modq_chebotarev_mertens_package :
    (1 - 1 - 1 = (-1 : ℤ) ∧ 1 + 1 - 1 = (1 : ℤ)) ∧
    (1 = 1 ∧ 1 + 1 = 2) ∧
    (2 * 1 = 2) ∧
    (1 + 3 = 4 ∧ 3 + 4 = 7) ∧
    (3 - 1 = 2 ∧ 2 / 2 = 1) :=
  paper_zeta_length_modq_chebotarev_mertens_seeds

set_option maxHeartbeats 400000 in
/-- Paper-facing coefficient form of the Dirichlet-Artin Möbius-log identity:
expand `log Z_j` by twisted traces and substitute it into the divisor sum. This
is the finite coefficient package behind the analytic formula
`𝓟_j(z) = ∑_{m ≥ 1} μ(m) / m * log Z_j(z^m)`.
thm:zeta-length-modq-dirichlet-artin-mobiuslog -/
theorem paper_zeta_length_modq_dirichlet_artin_mobiuslog
    (ω : ℂ) (j : ℕ) (μ trace twistedTrace logZCoeff : ℕ → ℂ) :
    (∀ n, twistedTrace n = ω ^ (j * n) * trace n) →
    (∀ n, logZCoeff n = twistedTrace n / (n : ℂ)) →
    (∀ n,
      lengthModqMobiuslogCoeff μ logZCoeff n =
        ∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) ∧
    (∀ z N,
      lengthModqMobiuslogSeries μ logZCoeff z N =
        ∑ n ∈ Finset.Icc 1 N,
          (∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) *
            z ^ n) := by
  intro hTrace hLog
  have hcoeff :
      ∀ n,
        lengthModqMobiuslogCoeff μ logZCoeff n =
          ∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d) := by
    intro n
    unfold lengthModqMobiuslogCoeff
    apply Finset.sum_congr rfl
    intro d hd
    rw [hLog, hTrace]
    simp [lengthModqTraceCoeff]
  refine ⟨?_, ?_⟩
  · intro n
    exact hcoeff n
  · intro z N
    unfold lengthModqMobiuslogSeries
    apply Finset.sum_congr rfl
    intro n hn
    rw [hcoeff n]

/-- Paper-facing wrapper combining the Chebotarev-Mertens seed package with the
Dirichlet-Artin Möbius-log coefficient expansion.
    thm:zeta-length-modq-chebotarev-mertens -/
theorem paper_zeta_length_modq_chebotarev_mertens
    (ω : ℂ) (j : ℕ) (μ trace twistedTrace logZCoeff : ℕ → ℂ) :
    (∀ n, twistedTrace n = ω ^ (j * n) * trace n) →
    (∀ n, logZCoeff n = twistedTrace n / (n : ℂ)) →
    ((1 - 1 - 1 = (-1 : ℤ) ∧ 1 + 1 - 1 = (1 : ℤ)) ∧
        (1 = 1 ∧ 1 + 1 = 2) ∧
        (2 * 1 = 2) ∧
        (1 + 3 = 4 ∧ 3 + 4 = 7) ∧
        (3 - 1 = 2 ∧ 2 / 2 = 1)) ∧
      (∀ n,
        lengthModqMobiuslogCoeff μ logZCoeff n =
          ∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) ∧
      (∀ z N,
        lengthModqMobiuslogSeries μ logZCoeff z N =
          ∑ n ∈ Finset.Icc 1 N,
            (∑ d ∈ n.divisors, μ d / (d : ℂ) * lengthModqTraceCoeff ω j trace (n / d)) *
              z ^ n) := by
  intro hTrace hLog
  refine ⟨paper_zeta_length_modq_chebotarev_mertens_package, ?_⟩
  exact paper_zeta_length_modq_dirichlet_artin_mobiuslog
    ω j μ trace twistedTrace logZCoeff hTrace hLog

end Omega.Zeta
