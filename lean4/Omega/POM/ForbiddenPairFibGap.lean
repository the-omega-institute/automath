import Mathlib.Tactic
import Omega.Combinatorics.FibonacciCube

namespace Omega.POM

/-- Paper label: `lem:pom-forbidden-pair-fib-gap`.
Via `xEquivPathIndSet`, counting path-independent sets containing the forced pairs `{2,5}` and
`{1,4}` is the same as counting stable words with the corresponding forced bits. The existing
two-point Fibonacci-cube count then gives the exact tail Fibonacci factors. -/
theorem paper_pom_forbidden_pair_fib_gap (k : ℕ) (hk : 5 ≤ k) :
    Fintype.card {S : Omega.PathIndSets k //
        ((⟨1, by omega⟩ : Fin k) ∈ S.1 ∧ (⟨4, by omega⟩ : Fin k) ∈ S.1)} = Nat.fib (k - 4) ∧
      Fintype.card {S : Omega.PathIndSets k //
        ((⟨0, by omega⟩ : Fin k) ∈ S.1 ∧ (⟨3, by omega⟩ : Fin k) ∈ S.1)} = Nat.fib (k - 3) := by
  classical
  let v0 : Fin k := ⟨0, by omega⟩
  let v1 : Fin k := ⟨1, by omega⟩
  let v3 : Fin k := ⟨3, by omega⟩
  let v4 : Fin k := ⟨4, by omega⟩
  let h25_equiv :
      {x : Omega.X k // x.1 v1 = true ∧ x.1 v4 = true} ≃
        {S : Omega.PathIndSets k // v1 ∈ S.1 ∧ v4 ∈ S.1} :=
    { toFun := fun x =>
        ⟨Omega.xEquivPathIndSet k x.1, by
          constructor <;> simp [Omega.xEquivPathIndSet, Omega.wordSupport, x.2.1, x.2.2]⟩
      invFun := fun S =>
        ⟨(Omega.xEquivPathIndSet k).symm S.1, by
          constructor <;> simp [Omega.xEquivPathIndSet, Omega.indSetToWord, S.2.1, S.2.2]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (Omega.xEquivPathIndSet k).left_inv x.1
      right_inv := by
        intro S
        apply Subtype.ext
        exact (Omega.xEquivPathIndSet k).right_inv S.1 }
  let h14_equiv :
      {x : Omega.X k // x.1 v0 = true ∧ x.1 v3 = true} ≃
        {S : Omega.PathIndSets k // v0 ∈ S.1 ∧ v3 ∈ S.1} :=
    { toFun := fun x =>
        ⟨Omega.xEquivPathIndSet k x.1, by
          constructor <;> simp [Omega.xEquivPathIndSet, Omega.wordSupport, x.2.1, x.2.2]⟩
      invFun := fun S =>
        ⟨(Omega.xEquivPathIndSet k).symm S.1, by
          constructor <;> simp [Omega.xEquivPathIndSet, Omega.indSetToWord, S.2.1, S.2.2]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        exact (Omega.xEquivPathIndSet k).left_inv x.1
      right_inv := by
        intro S
        apply Subtype.ext
        exact (Omega.xEquivPathIndSet k).right_inv S.1 }
  have h25 :
      Fintype.card {S : Omega.PathIndSets k // v1 ∈ S.1 ∧ v4 ∈ S.1} = Nat.fib (k - 4) := by
    rw [← Fintype.card_congr h25_equiv]
    calc
      Fintype.card {x : Omega.X k // x.1 v1 = true ∧ x.1 v4 = true}
          = Omega.twoPointCount k v1 v4 := by
              simp [Omega.twoPointCount, Fintype.card_subtype]
      _ = Nat.fib (v1.val + 1) * Nat.fib (v4.val - v1.val - 1) * Nat.fib (k - v4.val) := by
            exact Omega.twoPointCount_eq_fib_prod k v1 v4 (by simp [v1, v4]) (by simp [v1, v4])
      _ = Nat.fib (k - 4) := by
            norm_num [Nat.fib, v1, v4]
  have h14 :
      Fintype.card {S : Omega.PathIndSets k // v0 ∈ S.1 ∧ v3 ∈ S.1} = Nat.fib (k - 3) := by
    rw [← Fintype.card_congr h14_equiv]
    calc
      Fintype.card {x : Omega.X k // x.1 v0 = true ∧ x.1 v3 = true}
          = Omega.twoPointCount k v0 v3 := by
              simp [Omega.twoPointCount, Fintype.card_subtype]
      _ = Nat.fib (v0.val + 1) * Nat.fib (v3.val - v0.val - 1) * Nat.fib (k - v3.val) := by
            exact Omega.twoPointCount_eq_fib_prod k v0 v3 (by simp [v0, v3]) (by simp [v0, v3])
      _ = Nat.fib (k - 3) := by
            norm_num [Nat.fib, v0, v3]
  exact ⟨h25, h14⟩

end Omega.POM
