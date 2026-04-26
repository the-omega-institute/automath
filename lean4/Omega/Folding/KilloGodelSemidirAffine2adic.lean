import Mathlib.Data.List.OfFn
import Mathlib.Tactic
import Omega.Folding.KilloInfiniteStream2adicHolographicPoint
import Omega.Folding.KilloLeyang2powerTorsionCayleyHypercube

namespace Omega.Folding

private theorem killo_godel_semidir_affine_2adic_code_append {B q : ℕ} :
    ∀ l₁ l₂ : List (Fin q),
      killoCode B (l₁ ++ l₂) = killoCode B l₁ + B ^ l₁.length * killoCode B l₂
  | [], l₂ => by simp [killoCode]
  | d :: l₁, l₂ => by
      simp [killoCode, killo_godel_semidir_affine_2adic_code_append l₁ l₂, Nat.pow_succ,
        Nat.mul_add, Nat.mul_comm, Nat.mul_assoc, add_assoc]

private theorem killo_godel_semidir_affine_2adic_code_ofFn_injective {B q : ℕ} (hB : 0 < B)
    (hqB : q ≤ B) : ∀ n : ℕ, Function.Injective (fun u : Fin n → Fin q => killoCode B (List.ofFn u))
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
        killo_godel_semidir_affine_2adic_code_ofFn_injective hB hqB n htailCode
      funext i
      refine Fin.cases ?_ ?_ i
      · exact hhead
      · intro j
        simpa using congrFun htail j

/-- Paper label: `thm:killo-godel-semidir-affine-2adic`. The base-`B` address code is affine under
word concatenation, faithful on canonical digits when the digit alphabet fits inside the base, and
fails to be faithful already on two digits once a digit of size `B` is allowed.  Specializing to
`B = 2^L` recovers the existing infinite-stream `2`-adic holographic injectivity and the finite
`(ZMod (2^n))^2` address bijection. -/
theorem paper_killo_godel_semidir_affine_2adic :
    (∀ {B q : ℕ}, 0 < B → q ≤ B →
      ∀ n : ℕ, Function.Injective (fun u : Fin n → Fin q => killoCode B (List.ofFn u))) ∧
    (∀ {B q : ℕ}, 0 < B →
      ∀ l₁ l₂ : List (Fin q),
        killoCode B (l₁ ++ l₂) = killoCode B l₁ + B ^ l₁.length * killoCode B l₂) ∧
    (∀ L q : ℕ, q ≤ 2 ^ L →
      Function.Injective (killo_infinite_stream_2adic_holographic_point_truncation L q)) ∧
    (∀ n : ℕ, Function.Bijective (killo_leyang_2power_torsion_cayley_hypercube_address n)) ∧
    (∀ {B M : ℕ}, 0 < B → B ≤ M →
      ∃ u v : Fin 2 → Fin (M + 1),
        u ≠ v ∧ killoCode B (List.ofFn u) = killoCode B (List.ofFn v)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro B q hB hqB n
    exact killo_godel_semidir_affine_2adic_code_ofFn_injective hB hqB n
  · intro B q hB l₁ l₂
    exact killo_godel_semidir_affine_2adic_code_append l₁ l₂
  · intro L q hqB
    exact (paper_killo_infinite_stream_2adic_holographic_point L q hqB).2
  · intro n
    exact paper_killo_leyang_2power_torsion_cayley_hypercube n
  · intro B M hB hBM
    have hM : 0 < M := lt_of_lt_of_le hB hBM
    let zeroDigit : Fin (M + 1) := ⟨0, Nat.succ_pos _⟩
    let oneDigit : Fin (M + 1) := ⟨1, by omega⟩
    let bigDigit : Fin (M + 1) := ⟨B, by omega⟩
    let u : Fin 2 → Fin (M + 1) := fun i => if i.1 = 0 then zeroDigit else oneDigit
    let v : Fin 2 → Fin (M + 1) := fun i => if i.1 = 0 then bigDigit else zeroDigit
    refine ⟨u, v, ?_, ?_⟩
    · intro huv
      have h0 := congrArg Fin.val (congrFun huv 0)
      simp [u, v, zeroDigit, bigDigit] at h0
      omega
    · simp [u, v, killoCode, zeroDigit, oneDigit, bigDigit]

end Omega.Folding
