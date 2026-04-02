import Mathlib.Tactic

namespace Omega.Core

/-- Signed hypercube sum. -/
def signedHypercubeSum (n : Nat) (f : (Fin n → Bool) → ℤ) : ℤ :=
  ∑ w : Fin n → Bool,
    (-1 : ℤ) ^ ((Finset.univ.filter (fun i => w i = true)).card) * f w

/-- Constant signed sum vanishes for n ≥ 1.
    thm:discussion-walsh-stokes-higher-flux -/
theorem signedHypercubeSum_const (n : Nat) (hn : 1 ≤ n) (c : ℤ) :
    signedHypercubeSum n (fun _ => c) = 0 := by
  classical
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  let e : (Fin (m + 1) → Bool) ≃ (Fin m → Bool) × Bool :=
    { toFun := fun w => (fun i => w i.succ, w 0)
      invFun := fun p => Fin.cons p.2 p.1
      left_inv := by
        intro w
        funext i
        refine Fin.cases ?_ ?_ i
        · rfl
        · intro j
          rfl
      right_inv := by
        intro p
        cases p
        rfl }
  have hs :
      ∑ w : Fin (m + 1) → Bool,
        (-1 : ℤ) ^ ((Finset.univ.filter (fun i => w i = true)).card) * c
      =
      ∑ p : (Fin m → Bool) × Bool,
        (-1 : ℤ) ^ ((Finset.univ.filter (fun i => (e.symm p) i = true)).card) * c := by
    simpa [e] using
      (Fintype.sum_equiv e
        (fun w : Fin (m + 1) → Bool => (-1 : ℤ) ^ ((Finset.univ.filter (fun i => w i = true)).card) * c)
        (fun p : (Fin m → Bool) × Bool =>
          (-1 : ℤ) ^ ((Finset.univ.filter (fun i => (e.symm p) i = true)).card) * c)
        (by
          intro w
          simp [e]))
  have hs' : signedHypercubeSum (m + 1) (fun _ => c) =
      ∑ p : (Fin m → Bool) × Bool,
        (-1 : ℤ) ^ ((Finset.univ.filter (fun i => (e.symm p) i = true)).card) * c := by
    simpa [signedHypercubeSum] using hs
  change signedHypercubeSum (m + 1) (fun _ => c) = 0
  rw [hs']
  rw [Fintype.sum_prod_type]
  apply Finset.sum_eq_zero
  intro u hu
  rw [Fintype.sum_bool]
  simp [e, pow_succ, Int.neg_one_mul]

/-- One-dimensional test case.
    thm:discussion-walsh-stokes-higher-flux -/
theorem signedHypercubeSum_one :
    signedHypercubeSum 1 (fun w => if w 0 = true then 1 else 0) = -1 := by
  native_decide

end Omega.Core
