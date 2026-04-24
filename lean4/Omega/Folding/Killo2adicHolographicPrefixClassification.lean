import Mathlib

namespace Omega.Folding

/-- Infinite digit streams over an alphabet of size `q`. -/
abbrev KilloStream (q : ℕ) := ℕ → Fin q

/-- The length-`n` prefix of a stream. -/
def killoPrefix (q n : ℕ) (a : KilloStream q) : Fin n → Fin q := fun i => a i.1

/-- Least-significant-first base-`B` code attached to a prefix. -/
def killoCode (B : ℕ) : List (Fin q) → ℕ
  | [] => 0
  | d :: ds => d.1 + B * killoCode B ds

/-- The level-`n` residue readout of a stream. -/
def killoRho (B q n : ℕ) (a : KilloStream q) : ℕ :=
  killoCode B (List.ofFn (killoPrefix q n a))

/-- Effective level-`n` quotient image induced by the length-`n` prefixes. -/
def killoPrefixImage (B q n : ℕ) : Finset ℕ :=
  Finset.univ.image fun u : Fin n → Fin q => killoCode B (List.ofFn u)

private theorem killoCode_ofFn_injective {B q : ℕ} (hB : 0 < B) (hqB : q ≤ B) :
    ∀ n : ℕ, Function.Injective (fun u : Fin n → Fin q => killoCode B (List.ofFn u))
  | 0 => by
      intro u v _
      funext i
      exact Fin.elim0 i
  | n + 1 => by
      intro u v h
      change killoCode B (List.ofFn u) = killoCode B (List.ofFn v) at h
      rw [List.ofFn_succ, List.ofFn_succ, killoCode, killoCode] at h
      have huLt : (u 0).1 < B := lt_of_lt_of_le (u 0).2 hqB
      have hvLt : (v 0).1 < B := lt_of_lt_of_le (v 0).2 hqB
      have hmod :
          ((u 0).1 + B * killoCode B (List.ofFn fun i : Fin n => u i.succ)) % B =
            ((v 0).1 + B * killoCode B (List.ofFn fun i : Fin n => v i.succ)) % B := by
        exact congrArg (fun x => x % B) h
      have hheadVal : (u 0).1 = (v 0).1 := by
        calc
          (u 0).1 =
              ((u 0).1 + B * killoCode B (List.ofFn fun i : Fin n => u i.succ)) % B := by
                rw [Nat.add_mod]
                simp [Nat.mod_eq_of_lt huLt]
          _ =
              ((v 0).1 + B * killoCode B (List.ofFn fun i : Fin n => v i.succ)) % B := hmod
          _ = (v 0).1 := by
                rw [Nat.add_mod]
                simp [Nat.mod_eq_of_lt hvLt]
      have hhead : u 0 = v 0 := Fin.ext hheadVal
      rw [hhead] at h
      have htailMul :
          B * killoCode B (List.ofFn fun i : Fin n => u i.succ) =
            B * killoCode B (List.ofFn fun i : Fin n => v i.succ) := Nat.add_left_cancel h
      have htailCode :
          killoCode B (List.ofFn fun i : Fin n => u i.succ) =
            killoCode B (List.ofFn fun i : Fin n => v i.succ) := by
        rw [Nat.mul_comm B, Nat.mul_comm B] at htailMul
        exact Nat.mul_right_cancel hB htailMul
      have htail :
          (fun i : Fin n => u i.succ) = fun i : Fin n => v i.succ :=
        killoCode_ofFn_injective hB hqB n htailCode
      funext i
      refine Fin.cases ?_ ?_ i
      · exact hhead
      · intro j
        simpa using congrFun htail j

/-- Paper label: `prop:killo-2adic-holographic-prefix-classification`. In the concrete finite
prefix model, equality of the level-`n` quotient code is exactly equality of the first `n`
digits; consequently the quotient image has `q ^ n` points, and one fewer digit never separates
all length-`n` prefixes once the alphabet has at least two symbols. -/
theorem paper_killo_2adic_holographic_prefix_classification
    {B q : ℕ} (hB : 0 < B) (hqB : q ≤ B) :
    (∀ n : ℕ, ∀ a b : KilloStream q,
      killoRho B q n a = killoRho B q n b ↔ killoPrefix q n a = killoPrefix q n b) ∧
    (∀ n : ℕ, (killoPrefixImage B q n).card = q ^ n) ∧
    (1 < q → ∀ n : ℕ, 0 < n →
      ∃ a b : KilloStream q,
        killoRho B q (n - 1) a = killoRho B q (n - 1) b ∧
          killoPrefix q n a ≠ killoPrefix q n b) := by
  have hInjective :
      ∀ n : ℕ, Function.Injective (fun u : Fin n → Fin q => killoCode B (List.ofFn u)) :=
    killoCode_ofFn_injective hB hqB
  refine ⟨?_, ?_, ?_⟩
  · intro n a b
    constructor
    · intro h
      exact hInjective n h
    · intro hprefix
      simpa [killoRho, hprefix]
  · intro n
    calc
      (killoPrefixImage B q n).card =
          (Finset.univ : Finset (Fin n → Fin q)).card := by
            unfold killoPrefixImage
            exact Finset.card_image_of_injective _ (hInjective n)
      _ = Fintype.card (Fin n → Fin q) := by simp
      _ = q ^ n := by simp
  · intro hq1 n hn
    have hq0 : 0 < q := lt_trans Nat.zero_lt_one hq1
    let zeroDigit : Fin q := ⟨0, hq0⟩
    let oneDigit : Fin q := ⟨1, hq1⟩
    let a : KilloStream q := fun _ => zeroDigit
    let b : KilloStream q := fun i => if i = n - 1 then oneDigit else zeroDigit
    refine ⟨a, b, ?_, ?_⟩
    · have hprefix : killoPrefix q (n - 1) a = killoPrefix q (n - 1) b := by
        funext i
        simpa [killoPrefix, a, b, Nat.ne_of_lt i.2]
      simpa [killoRho, hprefix]
    · intro hEq
      have hlast := congrFun hEq ⟨n - 1, by omega⟩
      simp [killoPrefix, a, b] at hlast
      have h01 : (0 : ℕ) = 1 := by
        simpa [zeroDigit, oneDigit] using congrArg Fin.val hlast
      omega

end Omega.Folding
