import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic
import Omega.POM.CapacityCollisionDataProcessing

namespace Omega.OperatorAlgebra

open Finset

variable {Omega Y Z : Type*} [Fintype Omega] [Fintype Y] [Fintype Z]
variable [DecidableEq Y] [DecidableEq Z]

/-- The `q`-collision moment of a finite fold map. -/
def foldCollisionMoment (f : Omega → Y) (q : Nat) : Nat :=
  _root_.Omega.POM.collisionMoment f q

/-- The largest fiber cardinality of a finite coarse-graining map. -/
def foldMaxFiberCard (g : Y → Z) : Nat :=
  Finset.univ.sup fun z => _root_.Omega.POM.fiberCard g z

private lemma fiberCard_comp (f : Omega → Y) (g : Y → Z) (z : Z) :
    _root_.Omega.POM.fiberCard (g ∘ f) z =
      Finset.sum (Finset.univ.filter (fun y => g y = z)) (_root_.Omega.POM.fiberCard f) := by
  classical
  unfold _root_.Omega.POM.fiberCard
  calc
    Finset.sum Finset.univ (fun ω => if (g ∘ f) ω = z then (1 : ℕ) else 0)
      =
        Finset.sum Finset.univ fun ω =>
          Finset.sum (Finset.univ.filter (fun y => g y = z)) fun y =>
            if f ω = y then (1 : ℕ) else 0 := by
            refine Finset.sum_congr rfl ?_
            intro ω hω
            by_cases hz : g (f ω) = z
            · rw [Finset.sum_eq_single (f ω)]
              · simp [hz]
              · intro y hy hyf
                have : f ω ≠ y := by simpa using hyf.symm
                simp [this]
              · intro hmem
                simp [hz] at hmem
            · have hzero :
                ∀ y ∈ Finset.univ.filter (fun y => g y = z),
                  (if f ω = y then (1 : ℕ) else 0) = 0 := by
                intro y hy
                by_cases hyf : f ω = y
                · subst hyf
                  simp [hz] at hy
                · simp [hyf]
              simpa [hz] using Finset.sum_eq_zero hzero
    _ =
        Finset.sum (Finset.univ.filter (fun y => g y = z)) fun y =>
          Finset.sum Finset.univ (fun ω => if f ω = y then (1 : ℕ) else 0) := by
          rw [Finset.sum_comm]
    _ = Finset.sum (Finset.univ.filter (fun y => g y = z)) (_root_.Omega.POM.fiberCard f) := by
          simp [_root_.Omega.POM.fiberCard]

private lemma sum_over_fibers (g : Y → Z) (a : Y → ℕ) :
    Finset.sum Finset.univ (fun z => Finset.sum (Finset.univ.filter (fun y => g y = z)) a) =
      Finset.sum Finset.univ a := by
  classical
  calc
    Finset.sum Finset.univ (fun z => Finset.sum (Finset.univ.filter (fun y => g y = z)) a)
      = Finset.sum Finset.univ (fun z => Finset.sum Finset.univ (fun y => if g y = z then a y else 0)) := by
          refine Finset.sum_congr rfl ?_
          intro z hz
          rw [Finset.sum_filter]
    _ = Finset.sum Finset.univ (fun y => Finset.sum Finset.univ (fun z => if g y = z then a y else 0)) := by
          rw [Finset.sum_comm]
    _ = Finset.sum Finset.univ a := by
          refine Finset.sum_congr rfl ?_
          intro y hy
          rw [Finset.sum_eq_single (g y)]
          · simp
          · intro z hz hzy
            have : g y ≠ z := by simpa [eq_comm] using hzy
            simp [this]
          · intro hz
            simp at hz

private lemma filter_card_eq_fiberCard (g : Y → Z) (z : Z) :
    (Finset.univ.filter (fun y => g y = z)).card = _root_.Omega.POM.fiberCard g z := by
  classical
  unfold _root_.Omega.POM.fiberCard
  calc
    (Finset.univ.filter (fun y => g y = z)).card
      = Finset.sum (Finset.univ.filter (fun y => g y = z)) (fun _ => 1) := by
          exact Finset.card_eq_sum_ones _
    _ = Finset.sum Finset.univ (fun y => if g y = z then 1 else 0) := by rw [Finset.sum_filter]

private lemma fiberCard_le_foldMaxFiberCard (g : Y → Z) (z : Z) :
    _root_.Omega.POM.fiberCard g z ≤ foldMaxFiberCard g := by
  unfold foldMaxFiberCard
  exact Finset.le_sup (Finset.mem_univ z)

/-- Paper label: `prop:op-algebra-coarsegraining-sq-two-sided`. -/
theorem paper_op_algebra_coarsegraining_sq_two_sided {Omega Y Z : Type*} [Fintype Omega]
    [Fintype Y] [Fintype Z] [DecidableEq Y] [DecidableEq Z] (f : Omega → Y) (g : Y → Z)
    (q : Nat) (hq : 1 ≤ q) :
    foldCollisionMoment (g ∘ f) q >= foldCollisionMoment f q ∧
      foldCollisionMoment (g ∘ f) q <=
        foldMaxFiberCard g ^ (q - 1) * foldCollisionMoment f q := by
  constructor
  · simpa [foldCollisionMoment] using
      (_root_.Omega.POM.paper_pom_capacity_collision_data_processing f g 1 q (by decide) hq).2
  · unfold foldCollisionMoment
    calc
      Finset.sum Finset.univ (fun z => _root_.Omega.POM.fiberCard (g ∘ f) z ^ q)
        ≤
          Finset.sum Finset.univ fun z =>
            foldMaxFiberCard g ^ (q - 1) *
              Finset.sum (Finset.univ.filter (fun y => g y = z))
                (fun y => _root_.Omega.POM.fiberCard f y ^ q) := by
              refine Finset.sum_le_sum ?_
              intro z hz
              let s : Finset Y := Finset.univ.filter (fun y => g y = z)
              have hqpos : 0 < q := Nat.succ_le_iff.mp hq
              have hqsplit : q - 1 + 1 = q := Nat.succ_pred_eq_of_pos hqpos
              have hpow :
                  Finset.sum s (_root_.Omega.POM.fiberCard f) ^ q ≤
                    s.card ^ (q - 1) *
                      Finset.sum s (fun y => (_root_.Omega.POM.fiberCard f y) ^ q) := by
                simpa [s, hqsplit]
                  using
                    (pow_sum_le_card_mul_sum_pow
                      (s := s) (f := fun y => _root_.Omega.POM.fiberCard f y)
                      (hf := by
                        intro y hy
                        exact Nat.zero_le _)
                      (n := q - 1))
              have hcard :
                  s.card ^ (q - 1) ≤ foldMaxFiberCard g ^ (q - 1) := by
                rw [show s.card = _root_.Omega.POM.fiberCard g z by
                  simp [s, filter_card_eq_fiberCard]]
                exact Nat.pow_le_pow_left (fiberCard_le_foldMaxFiberCard g z) (q - 1)
              calc
                _root_.Omega.POM.fiberCard (g ∘ f) z ^ q =
                    Finset.sum s (_root_.Omega.POM.fiberCard f) ^ q := by
                  simp [s, fiberCard_comp]
                _ ≤ s.card ^ (q - 1) * Finset.sum s (fun y => _root_.Omega.POM.fiberCard f y ^ q) := hpow
                _ ≤
                    foldMaxFiberCard g ^ (q - 1) *
                      Finset.sum s (fun y => _root_.Omega.POM.fiberCard f y ^ q) := by
                  gcongr
      _ =
          foldMaxFiberCard g ^ (q - 1) *
            Finset.sum Finset.univ
              (fun z => Finset.sum (Finset.univ.filter (fun y => g y = z))
                (fun y => _root_.Omega.POM.fiberCard f y ^ q)) := by
            rw [Finset.mul_sum]
      _ = foldMaxFiberCard g ^ (q - 1) * Finset.sum Finset.univ (fun y => _root_.Omega.POM.fiberCard f y ^ q) := by
            rw [sum_over_fibers g (fun y => _root_.Omega.POM.fiberCard f y ^ q)]

end Omega.OperatorAlgebra
