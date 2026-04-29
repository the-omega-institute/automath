import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

namespace Omega.Conclusion

open scoped BigOperators

/-- The subset model for `Ω_m`. -/
abbrev FoldSubset (m : ℕ) := Finset (Fin m)

/-- The fiber over `x` in the fold map. -/
def foldFiber {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X] (fold : FoldSubset m → X) (x : X) :
    Finset (FoldSubset m) :=
  Finset.univ.filter fun ω => fold ω = x

/-- The hard-core partition function on one fiber, with activity `t`. -/
noncomputable def foldFiberPartition {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (fold : FoldSubset m → X)
    (reward : FoldSubset m → ℕ) (t : ℝ) (x : X) : ℝ :=
  Finset.sum (foldFiber fold x) fun ω => t ^ reward ω

/-- The annealed pushforward mass obtained by summing the activity weight `t^{|ω|}` over a fiber. -/
noncomputable def foldAnnealedPushforward {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (fold : FoldSubset m → X) (t : ℝ) (x : X) : ℝ :=
  Finset.sum (foldFiber fold x) fun ω => t ^ ω.card

/-- The fiberwise posterior after normalizing the annealed mass on the `x`-fiber. -/
noncomputable def foldAnnealedPosterior {m : ℕ} {X : Type*} [Fintype X] [DecidableEq X]
    (fold : FoldSubset m → X) (t : ℝ) (x : X) (ω : FoldSubset m) : ℝ :=
  t ^ ω.card / foldAnnealedPushforward fold t x

/-- Paper label: `thm:conclusion-fold-fiber-hardcore-annealed-conservation`.
If the subset cardinality splits as the visible occupation count plus a fiber reward, then the
annealed pushforward factorizes into the visible activity term times the hard-core fiber partition
function, the normalized fiber posterior is exactly the hard-core posterior, and summing over all
fibers recovers the global binomial partition function. -/
theorem paper_conclusion_fold_fiber_hardcore_annealed_conservation
    (m : ℕ) {X : Type*} [Fintype X] [DecidableEq X] (t : ℝ) (ht : 0 < t)
    (fold : FoldSubset m → X) (oneCount : X → ℕ) (reward : FoldSubset m → ℕ)
    (hsplit : ∀ ω : FoldSubset m, ω.card = oneCount (fold ω) + reward ω) :
    (∀ x : X,
      foldAnnealedPushforward fold t x =
        t ^ oneCount x * foldFiberPartition fold reward t x) ∧
      (∀ x : X, ∀ ω : FoldSubset m, fold ω = x →
        foldAnnealedPosterior fold t x ω = t ^ reward ω / foldFiberPartition fold reward t x) ∧
      ((∑ x : X, t ^ oneCount x * foldFiberPartition fold reward t x) = (1 + t) ^ m) := by
  have hpush :
      ∀ x : X, foldAnnealedPushforward fold t x = t ^ oneCount x * foldFiberPartition fold reward t x := by
    intro x
    unfold foldAnnealedPushforward foldFiberPartition foldFiber
    calc
      Finset.sum (Finset.univ.filter (fun ω : FoldSubset m => fold ω = x)) (fun ω => t ^ ω.card)
          = Finset.sum (Finset.univ.filter (fun ω : FoldSubset m => fold ω = x))
              (fun ω => t ^ oneCount x * t ^ reward ω) := by
                refine Finset.sum_congr rfl ?_
                intro ω hω
                have hx : fold ω = x := by simpa using (Finset.mem_filter.mp hω).2
                rw [hsplit ω, hx, pow_add]
      _ = t ^ oneCount x *
            Finset.sum (Finset.univ.filter (fun ω : FoldSubset m => fold ω = x))
              (fun ω => t ^ reward ω) := by
              rw [Finset.mul_sum]
  have hpost :
      ∀ x : X, ∀ ω : FoldSubset m, fold ω = x →
        foldAnnealedPosterior fold t x ω = t ^ reward ω / foldFiberPartition fold reward t x := by
    intro x ω hω
    have hbase_pos : 0 < t ^ oneCount x := pow_pos ht _
    have hpart_pos : 0 < foldFiberPartition fold reward t x := by
      unfold foldFiberPartition foldFiber
      have hterm : 0 < t ^ reward ω := pow_pos ht _
      have hle :
          t ^ reward ω ≤
            Finset.sum (Finset.univ.filter (fun η : FoldSubset m => fold η = x))
              (fun η => t ^ reward η) := by
              refine Finset.single_le_sum (f := fun η : FoldSubset m => t ^ reward η) ?_ ?_
              · intro η hη
                exact le_of_lt (pow_pos ht _)
              · simp [hω]
      exact lt_of_lt_of_le hterm hle
    have hpushx := hpush x
    calc
      foldAnnealedPosterior fold t x ω
          = (t ^ oneCount x * t ^ reward ω) /
              (t ^ oneCount x * foldFiberPartition fold reward t x) := by
                unfold foldAnnealedPosterior
                rw [hsplit ω, hω, pow_add, hpushx]
      _ = t ^ reward ω / foldFiberPartition fold reward t x := by
            field_simp [hbase_pos.ne', hpart_pos.ne']
  have hfiber :
      ∑ x : X, foldAnnealedPushforward fold t x = ∑ ω : FoldSubset m, t ^ ω.card := by
    classical
    simpa [foldAnnealedPushforward, foldFiber] using
      (Finset.sum_fiberwise_eq_sum_filter
        (s := (Finset.univ : Finset (FoldSubset m)))
        (t := (Finset.univ : Finset X))
        (g := fold)
        (f := fun ω : FoldSubset m => t ^ ω.card))
  have hglobal :
      ∑ x : X, t ^ oneCount x * foldFiberPartition fold reward t x = (1 + t) ^ m := by
    calc
      ∑ x : X, t ^ oneCount x * foldFiberPartition fold reward t x
          = ∑ x : X, foldAnnealedPushforward fold t x := by
              refine Finset.sum_congr rfl ?_
              intro x hx
              symm
              exact hpush x
      _ = ∑ ω : FoldSubset m, t ^ ω.card := hfiber
      _ = (1 + t) ^ m := by
            simpa [add_comm, mul_comm, mul_left_comm, mul_assoc] using
              (Fintype.sum_pow_mul_eq_add_pow (Fin m) t (1 : ℝ))
  exact ⟨hpush, hpost, hglobal⟩

end Omega.Conclusion
