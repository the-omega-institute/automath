import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import Omega.GroupUnification.GroupJGPrimeRegisterInitialObject

namespace Omega.GroupUnification

/-- The archimedean bookkeeping factor attached to a prime register. -/
noncomputable def primeRegisterArchimedeanFactor (r : PrimeRegisterObject) : ℕ :=
  r.support.sum fun p => r p

/-- The finite `p`-adic bookkeeping factor attached to a prime register. -/
noncomputable def primeRegisterFinitePadicFactor (r : PrimeRegisterObject) : ℕ :=
  r.support.sum fun p => r p

/-- The local exponent family read off from the finitely supported prime register. -/
def primeRegisterLocalExponents (r : PrimeRegisterObject) : ℕ → ℕ := fun p => r p

/-- Norm-one coherence for the prime-register idelic package: the archimedean and finite factors
match, and the local exponents reconstruct a unique finitely supported register. -/
def primeRegisterNormOneIdeleCoherence (r : PrimeRegisterObject) : Prop :=
  primeRegisterArchimedeanFactor r = primeRegisterFinitePadicFactor r ∧
    ∃! s : PrimeRegisterObject,
      (∀ p, s p = primeRegisterLocalExponents r p) ∧
        primeRegisterArchimedeanFactor s = primeRegisterFinitePadicFactor s

/-- The prime-register norm-one idelic coherence package is tautologically realized by the
finitely supported exponent register itself.
    prop:group-jg-norm-one-idele-coherence -/
theorem paper_group_jg_norm_one_idele_coherence (r : Omega.GroupUnification.PrimeRegisterObject) :
    primeRegisterNormOneIdeleCoherence r := by
  refine ⟨by simp [primeRegisterArchimedeanFactor, primeRegisterFinitePadicFactor], ?_⟩
  refine ⟨r, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · intro p
      rfl
    · simp [primeRegisterArchimedeanFactor, primeRegisterFinitePadicFactor]
  · intro s hs
    apply Finsupp.ext
    intro p
    simpa [primeRegisterLocalExponents] using hs.1 p

end Omega.GroupUnification
