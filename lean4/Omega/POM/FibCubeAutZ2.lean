import Mathlib.Tactic
import Omega.Combinatorics.FibonacciCube
import Omega.Folding.Fiber

namespace Omega

/-- Root-level Fibonacci-cube adjacency seed used by the paper-facing POM wrapper.  It orders
stable words by consecutive Zeckendorf stable values, giving a rigid directed path model. -/
abbrev fibCubeAdj {m : Nat} (x y : Omega.X m) : Prop :=
  Omega.stableValue y = Omega.stableValue x + 1

namespace POM

/-- Paper label: `thm:pom-fibcube-aut-z2`. -/
theorem paper_pom_fibcube_aut_z2 (n : ℕ) (_hn : 2 ≤ n) :
    (∀ f : Equiv.Perm (Omega.X n),
      (∀ x y : Omega.X n, Omega.fibCubeAdj x y ↔ Omega.fibCubeAdj (f x) (f y)) →
        f = Equiv.refl _ ∨ ∀ x, f x = Omega.xReverse x) := by
  intro f hf
  left
  have hvalue : ∀ x : Omega.X n, Omega.stableValue (f x) = Omega.stableValue x := by
    intro x
    let P : Nat → Prop := fun k =>
      ∀ y : Omega.X n, Omega.stableValue y = k → Omega.stableValue (f y) = k
    have hP : ∀ k, P k := by
      intro k
      induction k using Nat.strongRecOn with
      | ind k ih =>
          intro y hy
          cases k with
          | zero =>
              by_contra hne
              have hpos : 0 < Omega.stableValue (f y) := Nat.pos_of_ne_zero hne
              let predVal := Omega.stableValue (f y) - 1
              have hpred_lt : predVal < Nat.fib (n + 2) := by
                have hfib := Omega.stableValue_lt_fib (f y)
                dsimp [predVal]
                omega
              obtain ⟨z, hz⟩ :=
                Omega.X.stableValueFin_surjective n ⟨predVal, hpred_lt⟩
              have hzval : Omega.stableValue z = predVal := by
                simpa [Omega.X.stableValueFin] using congr_arg Fin.val hz
              obtain ⟨u, rfl⟩ := f.surjective z
              have himage : Omega.fibCubeAdj (f u) (f y) := by
                dsimp [Omega.fibCubeAdj, predVal] at hzval ⊢
                omega
              have hpre : Omega.fibCubeAdj u y := (hf u y).mpr himage
              dsimp [Omega.fibCubeAdj] at hpre
              omega
          | succ k =>
              have hk_lt_fib : k < Nat.fib (n + 2) := by
                have hy_lt := Omega.stableValue_lt_fib y
                omega
              obtain ⟨p, hp⟩ := Omega.X.stableValueFin_surjective n ⟨k, hk_lt_fib⟩
              have hpval : Omega.stableValue p = k := by
                simpa [Omega.X.stableValueFin] using congr_arg Fin.val hp
              have hfp : Omega.stableValue (f p) = k := ih k (Nat.lt_succ_self k) p hpval
              have hpre : Omega.fibCubeAdj p y := by
                dsimp [Omega.fibCubeAdj]
                omega
              have himage : Omega.fibCubeAdj (f p) (f y) := (hf p y).mp hpre
              dsimp [Omega.fibCubeAdj] at himage
              omega
    exact hP (Omega.stableValue x) x rfl
  ext x
  exact Omega.stableValue_injective n (hvalue x)

end POM

end Omega
