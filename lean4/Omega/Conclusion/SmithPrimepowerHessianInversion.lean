import Mathlib.Tactic

namespace Omega.Conclusion

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The reduced Smith loss profile at layer `k` is the total truncated valuation mass
across a finite valuation profile. -/
def lossProfile (valuation : α → ℕ) (k : ℕ) : ℕ :=
  ∑ x, min k (valuation x)

/-- The `k`-tail counts the layers whose valuation is at least `k`. -/
def tailCount (valuation : α → ℕ) (k : ℕ) : ℕ :=
  Fintype.card {x // k ≤ valuation x}

/-- The exact multiplicity of the valuation layer `k`. -/
def layerMultiplicity (valuation : α → ℕ) (k : ℕ) : ℕ :=
  Fintype.card {x // valuation x = k}

private lemma tailCount_eq_card_filter (valuation : α → ℕ) (k : ℕ) :
    tailCount valuation k = #{x | k ≤ valuation x} := by
  simpa [tailCount] using
    (Fintype.card_of_subtype (univ.filter fun x => k ≤ valuation x) (by
      intro x
      simp))

private lemma layerMultiplicity_eq_card_filter (valuation : α → ℕ) (k : ℕ) :
    layerMultiplicity valuation k = #{x | valuation x = k} := by
  simpa [layerMultiplicity] using
    (Fintype.card_of_subtype (univ.filter fun x => valuation x = k) (by
      intro x
      simp))

private lemma card_eq_tail_sub_tail_succ (valuation : α → ℕ) (k : ℕ) :
    (univ.filter fun x => valuation x = k).card =
      (univ.filter fun x => k ≤ valuation x).card -
        (univ.filter fun x => k + 1 ≤ valuation x).card := by
  let A : Finset α := univ.filter fun x => k ≤ valuation x
  let B : Finset α := univ.filter fun x => k + 1 ≤ valuation x
  have hBA : B ⊆ A := by
    intro x hx
    simp [A, B] at hx ⊢
    omega
  have hsplit : A \ B = univ.filter (fun x => valuation x = k) := by
    ext x
    simp [A, B]
    omega
  have hcard :
      (univ.filter fun x => valuation x = k).card = A.card - B.card := by
    rw [← hsplit, card_sdiff_of_subset hBA]
  simpa [A, B] using hcard

private lemma min_pred_add_tail_step (e k : ℕ) (hk : 1 ≤ k) :
    min (k - 1) e + (if k ≤ e then 1 else 0) = min k e := by
  by_cases hke : k ≤ e
  · have hpred : k - 1 ≤ e := by omega
    rw [Nat.min_eq_left hpred, Nat.min_eq_left hke]
    simp [hke]
    omega
  · have hek : e ≤ k - 1 := by omega
    rw [Nat.min_eq_right hek, Nat.min_eq_right (by omega : e ≤ k)]
    simp [hke]

/-- The first discrete difference of the loss profile is the tail count. -/
lemma lossProfile_step (valuation : α → ℕ) (k : ℕ) (hk : 1 ≤ k) :
    lossProfile valuation k = lossProfile valuation (k - 1) + tailCount valuation k := by
  rw [tailCount_eq_card_filter valuation k]
  calc
    lossProfile valuation k
        = ∑ x, (min (k - 1) (valuation x) + if k ≤ valuation x then 1 else 0) := by
            simp [lossProfile]
            apply sum_congr rfl
            intro x hx
            exact (min_pred_add_tail_step (valuation x) k hk).symm
    _ = (∑ x, min (k - 1) (valuation x)) + ∑ x, if k ≤ valuation x then 1 else 0 := by
          rw [sum_add_distrib]
    _ = lossProfile valuation (k - 1) + #{x | k ≤ valuation x} := by
          simp [lossProfile]

/-- The exact `k`-layer multiplicity is the difference of adjacent tail counts. -/
lemma layerMultiplicity_eq_tailDifference (valuation : α → ℕ) (k : ℕ) :
    layerMultiplicity valuation k = tailCount valuation k - tailCount valuation (k + 1) := by
  rw [layerMultiplicity_eq_card_filter, tailCount_eq_card_filter, tailCount_eq_card_filter]
  simpa using card_eq_tail_sub_tail_succ valuation k

/-- Paper label: `thm:conclusion-smith-primepower-hessian-inversion`.
The reduced loss profile has first difference equal to the valuation tail count, so its discrete
second difference recovers the exact multiplicity of each Smith valuation layer. -/
theorem paper_conclusion_smith_primepower_hessian_inversion (valuation : α → ℕ) :
    ∀ k : ℕ,
      1 ≤ k →
        layerMultiplicity valuation k =
          2 * lossProfile valuation k -
            lossProfile valuation (k - 1) - lossProfile valuation (k + 1) := by
  intro k hk
  have hstep := lossProfile_step valuation k hk
  have hstepSucc : lossProfile valuation (k + 1) =
      lossProfile valuation k + tailCount valuation (k + 1) := by
    simpa using lossProfile_step valuation (k + 1) (Nat.succ_le_succ (Nat.zero_le k))
  have hmult := layerMultiplicity_eq_tailDifference valuation k
  have htail :
      tailCount valuation k = lossProfile valuation k - lossProfile valuation (k - 1) := by
    omega
  have htailSucc :
      tailCount valuation (k + 1) = lossProfile valuation (k + 1) - lossProfile valuation k := by
    omega
  omega

end Omega.Conclusion
