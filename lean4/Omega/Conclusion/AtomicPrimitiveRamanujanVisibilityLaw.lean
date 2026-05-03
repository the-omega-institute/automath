import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.NumberTheory.Divisors

open scoped BigOperators

namespace Omega.Conclusion

/-- Concrete finite atom data for the primitive Ramanujan visibility law.  The atoms are indexed by
`Fin atomCount`; each atom has a length, a multiplicity-amplitude, and a phase monomial.  The
Ramanujan kernel is required to satisfy the finite divisor-indicator identity used by the sieve. -/
structure conclusion_atomic_primitive_ramanujan_visibility_law_data where
  atomCount : ℕ
  coreProjection : ℕ → ℂ
  coreDivisorSieve : ℕ → ℂ
  atomMultiplicity : Fin atomCount → ℂ
  atomLength : Fin atomCount → ℕ
  atomPhase : Fin atomCount → ℂ
  ramanujanCoefficient : ℕ → ℕ → ℂ
  ramanujanDivisorIndicator :
    ∀ r n : ℕ,
      (∑ q ∈ r.divisors, ramanujanCoefficient q n) = if r ∣ n then (1 : ℂ) else 0

namespace conclusion_atomic_primitive_ramanujan_visibility_law_data

/-- The finite atomic contribution in the `q`-th primitive Ramanujan projection. -/
def conclusion_atomic_primitive_ramanujan_visibility_law_primitive_ramanujan_atomic_contribution
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (q : ℕ) : ℂ :=
  ∑ j : Fin D.atomCount,
    D.atomMultiplicity j * D.ramanujanCoefficient q (D.atomLength j) * D.atomPhase j

/-- The total primitive Ramanujan projection after finite atomic surgery. -/
def conclusion_atomic_primitive_ramanujan_visibility_law_primitive_ramanujan_projection
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (q : ℕ) : ℂ :=
  D.coreProjection q +
    D.conclusion_atomic_primitive_ramanujan_visibility_law_primitive_ramanujan_atomic_contribution q

/-- The divisor-averaged atomic contribution before applying the indicator identity. -/
def conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atomic_contribution
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (r : ℕ) : ℂ :=
  ∑ j : Fin D.atomCount,
    D.atomMultiplicity j *
      (∑ q ∈ r.divisors, D.ramanujanCoefficient q (D.atomLength j)) *
        D.atomPhase j

/-- The total divisor-sieve layer obtained by averaging Ramanujan projections over divisors. -/
def conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (r : ℕ) : ℂ :=
  D.coreDivisorSieve r +
    D.conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atomic_contribution r

/-- The closed visibility form: only atoms whose length is divisible by `r` remain visible. -/
def conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_visible_atoms
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (r : ℕ) : ℂ :=
  ((Finset.univ : Finset (Fin D.atomCount)).filter (fun j => r ∣ D.atomLength j)).sum
    fun j => D.atomMultiplicity j * D.atomPhase j

/-- Projection formula for the finite core-plus-atoms decomposition. -/
def primitive_ramanujan_projection_formula
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) : Prop :=
  ∀ q : ℕ,
    D.conclusion_atomic_primitive_ramanujan_visibility_law_primitive_ramanujan_projection q =
      D.coreProjection q +
        D.conclusion_atomic_primitive_ramanujan_visibility_law_primitive_ramanujan_atomic_contribution q

/-- Divisor-sieve formula obtained from the Ramanujan divisor-indicator identity. -/
def divisor_sieve_formula
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) : Prop :=
  ∀ r : ℕ,
    D.conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve r =
      D.coreDivisorSieve r +
        D.conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_visible_atoms r

end conclusion_atomic_primitive_ramanujan_visibility_law_data

open conclusion_atomic_primitive_ramanujan_visibility_law_data

private lemma conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atoms
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) (r : ℕ) :
    D.conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atomic_contribution r =
      D.conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_visible_atoms r := by
  unfold conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atomic_contribution
    conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_visible_atoms
  simp [D.ramanujanDivisorIndicator r, mul_ite, Finset.sum_filter]

/-- Paper label: `thm:conclusion-atomic-primitive-ramanujan-visibility-law`. -/
theorem paper_conclusion_atomic_primitive_ramanujan_visibility_law
    (D : conclusion_atomic_primitive_ramanujan_visibility_law_data) :
    D.primitive_ramanujan_projection_formula /\ D.divisor_sieve_formula := by
  constructor
  · intro q
    rfl
  · intro r
    unfold conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve
    rw [conclusion_atomic_primitive_ramanujan_visibility_law_divisor_sieve_atoms]

end Omega.Conclusion
