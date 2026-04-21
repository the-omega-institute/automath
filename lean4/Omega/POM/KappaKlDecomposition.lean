import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Omega.POM.BeckChevalleyAmgmDefectIdentity

namespace Omega.POM

open scoped BigOperators

noncomputable section

section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The baseline weight `w_m(x) = d(x) / 2^m`. -/
noncomputable def baselineWeight (m : ℕ) (d : X → ℕ) (x : X) : ℝ :=
  d x / (2 ^ m : ℕ)

/-- The finite `κ_m(π) = E_π[log d(X)]` observable attached to a positive multiplicity profile. -/
noncomputable def kappa (d : X → ℕ) (π : X → ℝ) : ℝ :=
  ∑ x : X, π x * Real.log (d x)

/-- Unfolding `w_m(x) = d(x)/2^m` gives the exact identity
`κ_m(π) = m log 2 - H(π) - D_KL(π || w_m)`.
The usual upper bound and equality criterion then follow from KL nonnegativity and its zero
criterion.
    prop:pom-kappa-kl-decomposition -/
theorem paper_pom_kappa_kl_decomposition (m : ℕ) (d : X → ℕ) (hd : ∀ x, 0 < d x)
    (_hd_sum : ∑ x : X, d x = 2 ^ m) (π : X → ℝ) (hπ_nonneg : ∀ x, 0 ≤ π x)
    (hπ_sum : Finset.univ.sum π = 1) (hkl_nonneg : 0 ≤ klDiv π (baselineWeight m d))
    (hkl_zero_iff : klDiv π (baselineWeight m d) = 0 ↔ π = baselineWeight m d) :
    kappa d π = m * Real.log 2 - shannonEntropy π - klDiv π (baselineWeight m d) ∧
      kappa d π ≤ m * Real.log 2 - shannonEntropy π ∧
      (kappa d π = m * Real.log 2 - shannonEntropy π ↔ π = baselineWeight m d) := by
  have hpow0 : (((2 ^ m : ℕ) : ℝ) ≠ 0) := by
    exact_mod_cast pow_ne_zero m (show (2 : ℕ) ≠ 0 by decide)
  have hpowlog : Real.log (((2 ^ m : ℕ) : ℝ)) = m * Real.log 2 := by
    simpa using Real.log_pow (2 : ℝ) m
  have hExpand :
      klDiv π (baselineWeight m d) =
        ∑ x : X, (π x * Real.log (π x) - π x * Real.log (d x) + π x * (m * Real.log 2)) := by
    unfold klDiv baselineWeight
    refine Finset.sum_congr rfl ?_
    intro x hx
    have hd0 : (d x : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (hd x)
    by_cases hπ0 : π x = 0
    · simp [hπ0]
    · rw [Real.log_div hπ0 (div_ne_zero hd0 hpow0), Real.log_div hd0 hpow0, hpowlog]
      ring
  have hKl :
      klDiv π (baselineWeight m d) =
        m * Real.log 2 - shannonEntropy π - kappa d π := by
    calc
      klDiv π (baselineWeight m d) =
          ∑ x : X, (π x * Real.log (π x) - π x * Real.log (d x) + π x * (m * Real.log 2)) :=
        hExpand
      _ = (∑ x : X, π x * Real.log (π x)) - (∑ x : X, π x * Real.log (d x)) +
            ∑ x : X, π x * (m * Real.log 2) := by
            rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
      _ = (∑ x : X, π x * Real.log (π x)) - kappa d π +
            (∑ x : X, π x) * (m * Real.log 2) := by
            rw [kappa, ← Finset.sum_mul]
      _ = m * Real.log 2 - shannonEntropy π - kappa d π := by
            rw [hπ_sum, shannonEntropy]
            ring
  have hId : kappa d π = m * Real.log 2 - shannonEntropy π - klDiv π (baselineWeight m d) := by
    rw [hKl]
    ring
  have hUpper : kappa d π ≤ m * Real.log 2 - shannonEntropy π := by
    calc
      kappa d π = m * Real.log 2 - shannonEntropy π - klDiv π (baselineWeight m d) := hId
      _ ≤ m * Real.log 2 - shannonEntropy π := by
          linarith
  refine ⟨hId, hUpper, ?_⟩
  constructor
  · intro hEq
    have hzero :
        m * Real.log 2 - shannonEntropy π - klDiv π (baselineWeight m d) =
          m * Real.log 2 - shannonEntropy π := by
      simpa [hId] using hEq
    have hkl_zero : klDiv π (baselineWeight m d) = 0 := by
      linarith
    exact hkl_zero_iff.mp hkl_zero
  · intro hπ
    have hkl_zero : klDiv π (baselineWeight m d) = 0 := hkl_zero_iff.mpr hπ
    rw [hId, hkl_zero]
    ring

end

end

end Omega.POM
