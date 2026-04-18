import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic
import Omega.Zeta.SmithEntropyInvertsVpInvariants

namespace Omega.Zeta

open scoped BigOperators

/-- Tail counts decrease with the threshold. -/
lemma smithDelta_antitone (s : Multiset ℕ) {k ℓ : ℕ} (h : k ≤ ℓ) :
    smithDelta s ℓ ≤ smithDelta s k := by
  unfold smithDelta
  exact Multiset.card_le_card <|
    Multiset.monotone_filter_right s (by
      intro x hx
      exact le_trans h hx)

/-- Every element of a multiset of naturals is bounded by the total sum. -/
lemma le_sum_of_mem {v : ℕ} {s : Multiset ℕ} (hv : v ∈ s) : v ≤ s.sum := by
  induction s using Multiset.induction_on with
  | empty =>
      cases hv
  | @cons a t ih =>
      rw [Multiset.mem_cons] at hv
      rw [Multiset.sum_cons]
      rcases hv with rfl | hv
      · exact Nat.le_add_right _ _
      · exact le_trans (ih hv) (Nat.le_add_left _ _)

/-- The Smith delta of a replicate block is an indicator function. -/
lemma smithDelta_replicate (m a k : ℕ) :
    smithDelta (Multiset.replicate m a) k = if k ≤ a then m else 0 := by
  by_cases hk : k ≤ a
  · unfold smithDelta
    rw [if_pos hk, Multiset.filter_eq_self.2]
    · simp
    · intro b hb
      simpa [Multiset.eq_of_mem_replicate hb] using hk
  · unfold smithDelta
    rw [if_neg hk, Multiset.filter_eq_nil.2]
    · simp
    · intro b hb
      simpa [Multiset.eq_of_mem_replicate hb] using hk

/-- Smith deltas add under multiset addition. -/
lemma smithDelta_add (s t : Multiset ℕ) (k : ℕ) :
    smithDelta (s + t) k = smithDelta s k + smithDelta t k := by
  unfold smithDelta
  rw [Multiset.filter_add, Multiset.card_add]

/-- The finite multiset reconstructed from the discrete curvature of `f` up to level `N`. -/
def smithSpectrumApprox (f : ℕ → ℕ) (N : ℕ) : Multiset ℕ :=
  Finset.sum (Finset.range N) fun e =>
    Multiset.replicate ((f (e + 1) - f e) - (f (e + 2) - f (e + 1))) (e + 1)

lemma smithSpectrumApprox_succ (f : ℕ → ℕ) (N : ℕ) :
    smithSpectrumApprox f (N + 1) =
      smithSpectrumApprox f N +
        Multiset.replicate ((f (N + 1) - f N) - (f (N + 2) - f (N + 1))) (N + 1) := by
  simp [smithSpectrumApprox, Finset.sum_range_succ]

/-- Discrete concavity makes the first differences antitone. -/
lemma forwardDiff_antitone (f : ℕ → ℕ)
    (hconc : ∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) {k ℓ : ℕ} (h : k ≤ ℓ) :
    f (ℓ + 1) - f ℓ ≤ f (k + 1) - f k := by
  induction h with
  | refl =>
      exact le_rfl
  | @step n h ih =>
      exact le_trans (hconc n) ih

/-- The reconstructed finite multiset has the prescribed tail counts, up to the final cutoff. -/
lemma smithDelta_smithSpectrumApprox (f : ℕ → ℕ)
    (hconc : ∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) :
    ∀ N k : ℕ, k ≤ N →
      smithDelta (smithSpectrumApprox f N) (k + 1) =
        (f (k + 1) - f k) - (f (N + 1) - f N) := by
  intro N
  induction N with
  | zero =>
      intro k hk
      have hk0 : k = 0 := by omega
      subst hk0
      simp [smithSpectrumApprox, smithDelta]
  | succ N ih =>
      intro k hk
      rw [smithSpectrumApprox_succ, smithDelta_add]
      by_cases hkN : k ≤ N
      · rw [ih k hkN, smithDelta_replicate]
        have htail :
            f (N + 1) - f N ≤ f (k + 1) - f k := forwardDiff_antitone f hconc hkN
        have hstep :
            f (N + 2) - f (N + 1) ≤ f (N + 1) - f N := hconc N
        have hke : k + 1 ≤ N + 1 := Nat.succ_le_succ hkN
        rw [if_pos hke]
        have hab :
            ((f (k + 1) - f k) - (f (N + 1) - f N)) + (f (N + 1) - f N) = f (k + 1) - f k := by
          exact Nat.sub_add_cancel htail
        have hbc :
            ((f (N + 1) - f N) - (f (N + 2) - f (N + 1))) + (f (N + 2) - f (N + 1)) =
              f (N + 1) - f N := by
          exact Nat.sub_add_cancel hstep
        have htail' : f (N + 2) - f (N + 1) ≤ f (k + 1) - f k := le_trans hstep htail
        have hsum :
            (f (k + 1) - f k - (f (N + 1) - f N) +
                (f (N + 1) - f N - (f (N + 2) - f (N + 1))) +
                (f (N + 2) - f (N + 1))) =
              ((f (k + 1) - f k - (f (N + 2) - f (N + 1))) + (f (N + 2) - f (N + 1))) := by
          rw [Nat.add_assoc, hbc, hab, Nat.sub_add_cancel htail']
        exact Nat.add_right_cancel hsum
      · have hkEq : k = N + 1 := by omega
        subst hkEq
        have hzero :
            smithDelta (smithSpectrumApprox f N) (N + 2) = 0 := by
          have hbase := ih N le_rfl
          have hbase' : smithDelta (smithSpectrumApprox f N) (N + 1) = 0 := by
            simpa using hbase
          have hle : smithDelta (smithSpectrumApprox f N) (N + 2) ≤ 0 := by
            simpa [hbase'] using
              (smithDelta_antitone (s := smithSpectrumApprox f N) (Nat.le_succ (N + 1)))
          exact Nat.eq_zero_of_le_zero hle
        rw [hzero, smithDelta_replicate, if_neg (show ¬N + 2 ≤ N + 1 by omega)]
        simp

/-- Once the threshold passes the reconstruction cutoff, the recovered tail counts vanish. -/
lemma smithDelta_smithSpectrumApprox_zero_of_ge (f : ℕ → ℕ)
    (hconc : ∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) {N k : ℕ} (hk : N ≤ k) :
    smithDelta (smithSpectrumApprox f N) (k + 1) = 0 := by
  have hbase : smithDelta (smithSpectrumApprox f N) (N + 1) = 0 := by
    simpa using smithDelta_smithSpectrumApprox f hconc N N le_rfl
  have hle : smithDelta (smithSpectrumApprox f N) (k + 1) ≤ 0 := by
    simpa [hbase] using
      (smithDelta_antitone (s := smithSpectrumApprox f N) (Nat.succ_le_succ hk))
  exact Nat.eq_zero_of_le_zero hle

/-- A natural-valued function is a Smith entropy profile exactly when it starts at `0`, is
monotone, discretely concave, and eventually constant.
    thm:xi-smith-padic-loss-spectrum-classification -/
theorem paper_xi_smith_padic_loss_spectrum_classification (f : ℕ → ℕ) :
    (∃ s : Multiset ℕ, ∀ k : ℕ, f k = smithEntropy s k) ↔
      f 0 = 0 ∧
      (∀ k : ℕ, f k ≤ f (k + 1)) ∧
      (∀ k : ℕ, f (k + 2) - f (k + 1) ≤ f (k + 1) - f k) ∧
      ∃ N : ℕ, ∀ k : ℕ, N ≤ k → f (k + 1) = f k := by
  constructor
  · rintro ⟨s, hs⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [hs 0] using smithEntropy_zero s
    · intro k
      simpa [hs k, hs (k + 1)] using smithEntropy_mono_succ s k
    · intro k
      rw [hs (k + 2), hs (k + 1), hs k]
      rw [smithEntropy_succ_eq_add_delta s (k + 1), Nat.add_sub_cancel_left]
      rw [smithEntropy_succ_eq_add_delta s k, Nat.add_sub_cancel_left]
      exact smithDelta_antitone (s := s) (Nat.le_succ (k + 1))
    · refine ⟨s.sum, ?_⟩
      intro k hk
      have hk0 : ∀ v ∈ s, v ≤ k := by
        intro v hv
        exact le_trans (le_sum_of_mem hv) hk
      have hk1 : ∀ v ∈ s, v ≤ k + 1 := by
        intro v hv
        exact le_trans (hk0 v hv) (Nat.le_succ _)
      rw [hs (k + 1), hs k, smithEntropy_eq_sum_of_all_le s (k + 1) hk1,
        smithEntropy_eq_sum_of_all_le s k hk0]
  · rintro ⟨h0, hmono, hconc, ⟨N, hN⟩⟩
    refine ⟨smithSpectrumApprox f N, ?_⟩
    intro k
    induction k with
    | zero =>
        rw [h0, smithEntropy_zero]
    | succ k ih =>
        have hkdecomp : f (k + 1) = f k + (f (k + 1) - f k) := by
          exact (Nat.add_sub_of_le (hmono k)).symm
        have hdelta :
            smithDelta (smithSpectrumApprox f N) (k + 1) = f (k + 1) - f k := by
          by_cases hkN : k ≤ N
          · rw [smithDelta_smithSpectrumApprox f hconc N k hkN]
            have hcut : f (N + 1) - f N = 0 := by
              simpa [hN N le_rfl]
            simp [hcut]
          · have hNk : N ≤ k := by omega
            have hconst : f (k + 1) = f k := hN k hNk
            have hcut : f (k + 1) - f k = 0 := by simpa [hconst]
            rw [smithDelta_smithSpectrumApprox_zero_of_ge f hconc hNk, hcut]
        calc
          f (k + 1) = f k + (f (k + 1) - f k) := hkdecomp
          _ = smithEntropy (smithSpectrumApprox f N) k + (f (k + 1) - f k) := by rw [ih]
          _ = smithEntropy (smithSpectrumApprox f N) k +
                smithDelta (smithSpectrumApprox f N) (k + 1) := by rw [← hdelta]
          _ = smithEntropy (smithSpectrumApprox f N) (k + 1) := by
                symm
                exact smithEntropy_succ_eq_add_delta (smithSpectrumApprox f N) k

end Omega.Zeta
