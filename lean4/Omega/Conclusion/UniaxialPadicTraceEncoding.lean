import Mathlib.Data.Fin.Tuple.Take
import Mathlib.Data.Nat.Digits.Lemmas
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Conclusion

noncomputable section

/-- Paper label: `prop:conclusion-uniaxial-padic-trace-encoding`. -/
def conclusion_uniaxial_padic_trace_encoding_digit (E : Type*) [Fintype E] (e : E) : ℕ :=
  (Fintype.equivFin E e).val

theorem conclusion_uniaxial_padic_trace_encoding_digit_lt_card (E : Type*) [Fintype E]
    (e : E) :
    conclusion_uniaxial_padic_trace_encoding_digit E e < Fintype.card E :=
  (Fintype.equivFin E e).isLt

/-- Paper label: `prop:conclusion-uniaxial-padic-trace-encoding`. -/
def conclusion_uniaxial_padic_trace_encoding_digits (E : Type*) [Fintype E] (N : ℕ)
    (w : Fin N → E) : List ℕ :=
  List.ofFn fun i => conclusion_uniaxial_padic_trace_encoding_digit E (w i)

theorem conclusion_uniaxial_padic_trace_encoding_digits_lt_base (E : Type*) [Fintype E]
    {p N : ℕ} (hcard : Fintype.card E < p) (w : Fin N → E) :
    ∀ d ∈ conclusion_uniaxial_padic_trace_encoding_digits E N w, d < p := by
  rw [conclusion_uniaxial_padic_trace_encoding_digits]
  simpa [List.forall_mem_ofFn_iff] using
    (fun i : Fin N =>
      lt_trans (conclusion_uniaxial_padic_trace_encoding_digit_lt_card E (w i)) hcard)

/-- Paper label: `prop:conclusion-uniaxial-padic-trace-encoding`. -/
def conclusion_uniaxial_padic_trace_encoding_encode (E : Type*) [Fintype E]
    (p N : ℕ) (hp : 1 < p) (hcard : Fintype.card E < p) (w : Fin N → E) :
    Fin (p ^ N) :=
  ⟨Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E N w), by
    simpa [conclusion_uniaxial_padic_trace_encoding_digits] using
      Nat.ofDigits_lt_base_pow_length hp
        (conclusion_uniaxial_padic_trace_encoding_digits_lt_base E hcard w)⟩

theorem conclusion_uniaxial_padic_trace_encoding_digits_injective (E : Type*) [Fintype E]
    {N : ℕ} :
    Function.Injective (conclusion_uniaxial_padic_trace_encoding_digits E N) := by
  intro w v h
  have conclusion_uniaxial_padic_trace_encoding_digit_fun_eq :
      (fun i : Fin N => conclusion_uniaxial_padic_trace_encoding_digit E (w i)) =
        fun i : Fin N => conclusion_uniaxial_padic_trace_encoding_digit E (v i) := by
    exact List.ofFn_injective h
  funext i
  apply (Fintype.equivFin E).injective
  apply Fin.ext
  exact congrFun conclusion_uniaxial_padic_trace_encoding_digit_fun_eq i

theorem conclusion_uniaxial_padic_trace_encoding_ofDigits_injective (E : Type*) [Fintype E]
    {p N : ℕ} (hp : 1 < p) (hcard : Fintype.card E < p) :
    Function.Injective fun w : Fin N → E =>
      Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E N w) := by
  intro w v h
  apply conclusion_uniaxial_padic_trace_encoding_digits_injective E
  exact Nat.ofDigits_inj_of_len_eq hp (by simp [conclusion_uniaxial_padic_trace_encoding_digits])
    (conclusion_uniaxial_padic_trace_encoding_digits_lt_base E hcard w)
    (conclusion_uniaxial_padic_trace_encoding_digits_lt_base E hcard v) h

theorem conclusion_uniaxial_padic_trace_encoding_take_digits (E : Type*) [Fintype E]
    {M N : ℕ} (hMN : M ≤ N) (w : Fin N → E) (v : Fin M → E)
    (hprefix : ∀ i : Fin M, v i = w ⟨i.1, Nat.lt_of_lt_of_le i.2 hMN⟩) :
    conclusion_uniaxial_padic_trace_encoding_digits E M v =
      (conclusion_uniaxial_padic_trace_encoding_digits E N w).take M := by
  calc
    conclusion_uniaxial_padic_trace_encoding_digits E M v =
        conclusion_uniaxial_padic_trace_encoding_digits E M
          (fun i : Fin M => w ⟨i.1, Nat.lt_of_lt_of_le i.2 hMN⟩) := by
        apply congrArg
        funext i
        exact hprefix i
    _ = (conclusion_uniaxial_padic_trace_encoding_digits E N w).take M := by
        simpa [conclusion_uniaxial_padic_trace_encoding_digits, Fin.take] using
          (Fin.ofFn_take_eq_take_ofFn hMN
            (fun i : Fin N => conclusion_uniaxial_padic_trace_encoding_digit E (w i)))

theorem conclusion_uniaxial_padic_trace_encoding_mod_compat (E : Type*) [Fintype E]
    {p M N : ℕ} (hp : 1 < p) (hcard : Fintype.card E < p) (hMN : M ≤ N)
    (w : Fin N → E) (v : Fin M → E)
    (hprefix : ∀ i : Fin M, v i = w ⟨i.1, Nat.lt_of_lt_of_le i.2 hMN⟩) :
    Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E N w) % (p ^ M) =
      Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E M v) := by
  let L := conclusion_uniaxial_padic_trace_encoding_digits E N w
  let L₀ := conclusion_uniaxial_padic_trace_encoding_digits E M v
  have conclusion_uniaxial_padic_trace_encoding_take :
      L₀ = L.take M :=
    conclusion_uniaxial_padic_trace_encoding_take_digits E hMN w v hprefix
  have conclusion_uniaxial_padic_trace_encoding_L_digits : ∀ d ∈ L, d < p := by
    intro d hd
    exact conclusion_uniaxial_padic_trace_encoding_digits_lt_base E hcard w d (by
      simpa [L] using hd)
  calc
    Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E N w) % (p ^ M)
        = Nat.ofDigits p L % (p ^ M) := rfl
    _ = Nat.ofDigits p (L.take M) := by
        rw [Nat.ofDigits_mod_pow_eq_ofDigits_take M (Nat.zero_lt_of_lt hp) L
          conclusion_uniaxial_padic_trace_encoding_L_digits]
    _ = Nat.ofDigits p (conclusion_uniaxial_padic_trace_encoding_digits E M v) := by
        exact congrArg (Nat.ofDigits p) conclusion_uniaxial_padic_trace_encoding_take.symm

/-- Paper label: `prop:conclusion-uniaxial-padic-trace-encoding`. -/
theorem paper_conclusion_uniaxial_padic_trace_encoding (E : Type*) [Fintype E]
    [DecidableEq E] :
    ∃ p : Nat, Nat.Prime p ∧ Fintype.card E < p ∧
      ∃ encPrefix : (N : Nat) → (Fin N → E) → Fin (p ^ N),
        (∀ N, Function.Injective (encPrefix N)) ∧
          ∀ {M N : Nat} (hMN : M ≤ N) (w : Fin N → E) (v : Fin M → E),
            (∀ i : Fin M, v i = w ⟨i.1, Nat.lt_of_lt_of_le i.2 hMN⟩) →
              (encPrefix N w).val % (p ^ M) = (encPrefix M v).val := by
  obtain ⟨p, hlep, hpprime⟩ := Nat.exists_infinite_primes (Fintype.card E + 1)
  have hpcard : Fintype.card E < p := Nat.lt_of_succ_le hlep
  have hpbase : 1 < p := hpprime.one_lt
  refine ⟨p, hpprime, hpcard, ?_⟩
  refine ⟨fun N w =>
    conclusion_uniaxial_padic_trace_encoding_encode E p N hpbase hpcard w, ?_, ?_⟩
  · intro N w v h
    apply conclusion_uniaxial_padic_trace_encoding_ofDigits_injective E hpbase hpcard
    exact congrArg Fin.val h
  · intro M N hMN w v hprefix
    exact conclusion_uniaxial_padic_trace_encoding_mod_compat E hpbase hpcard hMN w v hprefix

end

end Omega.Conclusion
