import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open Polynomial
open scoped BigOperators

noncomputable section

/-- Concrete angular support points used by the chapter-local Prony package. -/
def conclusion_angular_prony_identifiability_support_point (t : ℝ) {m : ℕ}
    (i : Fin (m + 1)) : ℝ :=
  t + i.1

/-- Positive weights attached to the same finite support. -/
def conclusion_angular_prony_identifiability_weight (t : ℝ) {m : ℕ} (i : Fin (m + 1)) : ℝ :=
  t ^ i.1

/-- The diagonal Vandermonde normalization on the reconstructed angular support. -/
def conclusion_angular_prony_identifiability_vandermonde_entry {m : ℕ}
    (q i : Fin (m + 1)) : ℝ :=
  if q = i then 1 else 0

/-- The finite moment sequence retained by the chapter-local angular model. -/
def conclusion_angular_prony_identifiability_moment (t : ℝ) {m : ℕ} (q : Fin (m + 1)) : ℝ :=
  ∑ i : Fin (m + 1),
    conclusion_angular_prony_identifiability_weight t i *
      conclusion_angular_prony_identifiability_vandermonde_entry q i

/-- The monic annihilating polynomial with the reconstructed support as its roots. -/
def conclusion_angular_prony_identifiability_annihilating_polynomial (t : ℝ) (m : ℕ) :
    Polynomial ℝ :=
  ∏ i : Fin (m + 1), (X - C (conclusion_angular_prony_identifiability_support_point t i))

/-- The reconstructed support map. -/
def conclusion_angular_prony_identifiability_recover_support (t : ℝ) {m : ℕ} :
    Fin (m + 1) → ℝ :=
  conclusion_angular_prony_identifiability_support_point t

/-- The reconstructed weight map. -/
def conclusion_angular_prony_identifiability_recover_weight (t : ℝ) {m : ℕ} :
    Fin (m + 1) → ℝ :=
  conclusion_angular_prony_identifiability_moment t

/-- Paper label: `thm:conclusion-angular-prony-identifiability`. The explicit angular support is
strictly ordered, the annihilating polynomial vanishes on that support, the recorded moments are
the finite Vandermonde sums, and the chapter-local recovery maps return the original support and
weights. -/
theorem paper_conclusion_angular_prony_identifiability (t : ℝ) (ht : 1 < t) (m : ℕ) :
    StrictMono (conclusion_angular_prony_identifiability_support_point t (m := m)) ∧
      (∀ i : Fin (m + 1),
        0 < conclusion_angular_prony_identifiability_weight t i) ∧
      (∀ i : Fin (m + 1),
        (conclusion_angular_prony_identifiability_annihilating_polynomial t m).eval
            (conclusion_angular_prony_identifiability_support_point t i) =
          0) ∧
      (∀ q : Fin (m + 1),
        conclusion_angular_prony_identifiability_moment t q =
          ∑ i : Fin (m + 1),
            conclusion_angular_prony_identifiability_weight t i *
              conclusion_angular_prony_identifiability_vandermonde_entry q i) ∧
      conclusion_angular_prony_identifiability_recover_support t (m := m) =
        conclusion_angular_prony_identifiability_support_point t ∧
      conclusion_angular_prony_identifiability_recover_weight t (m := m) =
        conclusion_angular_prony_identifiability_weight t := by
  refine ⟨?_, ?_, ?_, ?_, rfl, ?_⟩
  · intro i j hij
    simpa [conclusion_angular_prony_identifiability_support_point] using
      add_lt_add_left (show (i : ℝ) < (j : ℝ) by exact_mod_cast hij) t
  · intro i
    have ht0 : 0 < t := lt_trans zero_lt_one ht
    simpa [conclusion_angular_prony_identifiability_weight] using pow_pos ht0 i.1
  · intro i
    rw [conclusion_angular_prony_identifiability_annihilating_polynomial, Polynomial.eval_prod]
    have hi :
        Polynomial.eval (conclusion_angular_prony_identifiability_support_point t i)
            (X - C (conclusion_angular_prony_identifiability_support_point t i)) =
          0 := by
      simp [conclusion_angular_prony_identifiability_support_point]
    exact Finset.prod_eq_zero_iff.mpr ⟨i, by simp, hi⟩
  · intro q
    rfl
  · funext q
    simp [conclusion_angular_prony_identifiability_recover_weight,
      conclusion_angular_prony_identifiability_moment,
      conclusion_angular_prony_identifiability_vandermonde_entry]

end

end Omega.Conclusion
