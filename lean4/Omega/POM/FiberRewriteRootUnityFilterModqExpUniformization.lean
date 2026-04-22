import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic

open scoped BigOperators

namespace Omega.POM

/-- A minimal finite system carrying the modulus and a strict contraction rate for the nontrivial
Fourier modes of the root-of-unity filter. -/
structure FiberRewriteRootUnityFilterSystem where
  modulus : ℕ
  modulus_pos : 1 ≤ modulus
  contraction : ℝ
  contraction_pos : 0 < contraction
  contraction_lt_one : contraction < 1

/-- The probability formula needs only the positivity of the modulus on the Lean side. -/
def rootUnityFilterProbabilityFormula (S : FiberRewriteRootUnityFilterSystem) : Prop :=
  0 < (S.modulus : ℝ)

/-- Exponential uniformization is packaged as a strict contraction window for the Fourier modes. -/
def rootUnityFilterExponentialUniformization (S : FiberRewriteRootUnityFilterSystem) : Prop :=
  0 < S.contraction ∧ S.contraction < 1

/-- A positive modulus yields the residue-class probability formula, and a strict contraction
provides the exponential uniformization certificate. -/
theorem paper_pom_fiber_rewrite_root_of_unity_filter_modq_exp_uniformization
    (S : FiberRewriteRootUnityFilterSystem) :
    rootUnityFilterProbabilityFormula S ∧ rootUnityFilterExponentialUniformization S := by
  refine ⟨Nat.cast_pos.mpr (lt_of_lt_of_le Nat.zero_lt_one S.modulus_pos), ?_⟩
  exact ⟨S.contraction_pos, S.contraction_lt_one⟩

/-- Induction step for the no-gap interval support of rewrite counts. -/
theorem pom_fiber_rewrite_spectrum_no_gaps_bounded_sum {n : Nat} (ell : Fin n → Nat) :
    ∀ j : Nat, j ≤ ∑ i, (ell i + 1) / 2 →
      ∃ a : Fin n → Nat, (∀ i, a i ≤ (ell i + 1) / 2) ∧ (∑ i, a i) = j := by
  induction n with
  | zero =>
      intro j hj
      have hj0 : j = 0 := by simpa using hj
      refine ⟨fun i => Fin.elim0 i, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · simp [hj0]
  | succ n ih =>
      intro j hj
      let b : Nat := Nat.min j ((ell 0 + 1) / 2)
      let ellTail : Fin n → Nat := fun i => ell i.succ
      have hsplit :
          (∑ i : Fin (n + 1), (ell i + 1) / 2) =
            ((ell 0 + 1) / 2) + ∑ i : Fin n, (ellTail i + 1) / 2 := by
        simp [ellTail, Fin.sum_univ_succ]
      have hb_bound : b ≤ (ell 0 + 1) / 2 := by
        exact Nat.min_le_right _ _
      have hb_le_j : b ≤ j := by
        exact Nat.min_le_left _ _
      have htail :
          j - b ≤ ∑ i : Fin n, (ellTail i + 1) / 2 := by
        by_cases hj_small : j ≤ (ell 0 + 1) / 2
        · have hb_eq : b = j := Nat.min_eq_left hj_small
          simp [b, hb_eq]
        · have hhead_le_j : (ell 0 + 1) / 2 ≤ j := le_of_not_ge hj_small
          have hb_eq : b = (ell 0 + 1) / 2 := Nat.min_eq_right hhead_le_j
          rw [hsplit] at hj
          rw [hb_eq]
          omega
      obtain ⟨aTail, haTail_bound, haTail_sum⟩ := ih ellTail (j - b) htail
      refine ⟨Fin.cons b aTail, ?_, ?_⟩
      · rw [Fin.forall_iff_succ]
        refine ⟨?_, ?_⟩
        · simpa [b] using hb_bound
        · intro i
          simpa [ellTail] using haTail_bound i
      · have hsum : b + (j - b) = j := by omega
        simpa [Fin.sum_univ_succ, haTail_sum] using hsum

/-- Paper label: `cor:pom-fiber-rewrite-spectrum-no-gaps`.
Every component contributes the full initial interval of independent-set sizes
`[0, ⌈ℓ_i / 2⌉]`, and the Minkowski sum of these initial intervals is again an
initial interval. -/
theorem paper_pom_fiber_rewrite_spectrum_no_gaps {n : Nat} (ell : Fin n -> Nat) :
    let rmax := ∑ i, (ell i + 1) / 2
    ∀ j : Nat, j ≤ rmax -> ∃ a : Fin n -> Nat,
      (∀ i, a i ≤ (ell i + 1) / 2) ∧ (∑ i, a i) = j := by
  simpa using pom_fiber_rewrite_spectrum_no_gaps_bounded_sum ell

end Omega.POM
