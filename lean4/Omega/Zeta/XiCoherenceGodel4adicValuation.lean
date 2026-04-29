import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Fin.Tuple.Take
import Omega.Zeta.XiCoherenceAffineSubcube

namespace Omega.Zeta

/-- Base-`4` Gödel code of a quaternary word, with the first coordinate in the units digit. -/
def xi_coherence_godel_4adic_valuation_code (N : ℕ) (x : Fin N → Fin 4) : ℕ :=
  Nat.ofDigits 4 (List.ofFn fun i : Fin N => (x i).val)

lemma xi_coherence_godel_4adic_valuation_split_first
    (N m : ℕ) (hm : m ≤ N) (x : Fin N → Fin 4) :
    (xi_coherence_affine_subcube_splitEquiv N m hm x).1 = Fin.take m hm x := by
  ext i
  congr

lemma xi_coherence_godel_4adic_valuation_digits_lt
    (N : ℕ) (x : Fin N → Fin 4) :
    ∀ a ∈ List.ofFn (fun i : Fin N => (x i).val), a < 4 := by
  intro a ha
  rw [List.mem_ofFn'] at ha
  rcases ha with ⟨i, rfl⟩
  exact (x i).isLt

lemma xi_coherence_godel_4adic_valuation_mod_eq_take
    (N m : ℕ) (hm : m ≤ N) (x y : Fin N → Fin 4) :
    xi_coherence_godel_4adic_valuation_code N x % 4 ^ m =
        xi_coherence_godel_4adic_valuation_code N y % 4 ^ m ↔
      Fin.take m hm x = Fin.take m hm y := by
  unfold xi_coherence_godel_4adic_valuation_code
  rw [Nat.ofDigits_mod_pow_eq_ofDigits_take m (by omega : 0 < 4)
      (List.ofFn fun i : Fin N => (x i).val),
    Nat.ofDigits_mod_pow_eq_ofDigits_take m (by omega : 0 < 4)
      (List.ofFn fun i : Fin N => (y i).val)]
  · constructor
    · intro h
      have hList :
          (List.ofFn fun i : Fin N => (x i).val).take m =
            (List.ofFn fun i : Fin N => (y i).val).take m := by
        exact Nat.ofDigits_inj_of_len_eq (by omega : 1 < 4) (by simp [hm])
          (by
            intro a ha
            exact xi_coherence_godel_4adic_valuation_digits_lt N x a
              ((List.take_prefix m _).subset ha))
          (by
            intro a ha
            exact xi_coherence_godel_4adic_valuation_digits_lt N y a
              ((List.take_prefix m _).subset ha))
          h
      have hVal :
          Fin.take m hm (fun i : Fin N => (x i).val) =
            Fin.take m hm (fun i : Fin N => (y i).val) := by
        apply List.ofFn_injective
        simpa [Fin.ofFn_take_eq_take_ofFn hm] using hList
      ext i
      exact congrFun hVal i
    · intro h
      have hVal :
          Fin.take m hm (fun i : Fin N => (x i).val) =
            Fin.take m hm (fun i : Fin N => (y i).val) := by
        ext i
        exact congrArg Fin.val (congrFun h i)
      rw [← Fin.ofFn_take_eq_take_ofFn hm, ← Fin.ofFn_take_eq_take_ofFn hm]
      exact congrArg (Nat.ofDigits 4) (congrArg List.ofFn hVal)
  · exact xi_coherence_godel_4adic_valuation_digits_lt N y
  · exact xi_coherence_godel_4adic_valuation_digits_lt N x

/-- Paper label: `thm:xi-coherence-godel-4adic-valuation`. -/
theorem paper_xi_coherence_godel_4adic_valuation
    (N m : ℕ) (hm : m ≤ N) (x y : Fin N → Fin 4) :
    xi_coherence_godel_4adic_valuation_code N x % 4 ^ m =
        xi_coherence_godel_4adic_valuation_code N y % 4 ^ m ↔
      (xi_coherence_affine_subcube_splitEquiv N m hm x).1 =
        (xi_coherence_affine_subcube_splitEquiv N m hm y).1 := by
  rw [xi_coherence_godel_4adic_valuation_mod_eq_take N m hm x y,
    xi_coherence_godel_4adic_valuation_split_first N m hm x,
    xi_coherence_godel_4adic_valuation_split_first N m hm y]

end Omega.Zeta
