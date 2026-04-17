import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic
import Omega.POM.FractranTwoPrimeDenominatorDfaCompile

namespace Omega.POM

private lemma primecoreStep_eq_of_exists_unique
    {F : List (Nat × Nat)} {a d : Nat}
    (hex : ∃ instr ∈ F, instr.2 ∣ d)
    (hu : ∀ {a' d'}, (a', d') ∈ F → d' ∣ d → a' * (d / d') = a) :
    primecoreStep F d = a := by
  induction F with
  | nil =>
      rcases hex with ⟨_, hmem, _⟩
      cases hmem
  | cons x xs ih =>
      by_cases hdiv : x.2 ∣ d
      · have hx : x.1 * (d / x.2) = a := hu (by simp) hdiv
        simp [primecoreStep, hdiv, hx]
      · have hex' : ∃ instr ∈ xs, instr.2 ∣ d := by
          rcases hex with ⟨instr, hmem, hInstrDiv⟩
          simp at hmem
          rcases hmem with rfl | hmemTail
          · exact False.elim (hdiv hInstrDiv)
          · exact ⟨instr, hmemTail, hInstrDiv⟩
        have hu' : ∀ {a' d'}, (a', d') ∈ xs → d' ∣ d → a' * (d / d') = a := by
          intro a' d' hmem hdvd
          exact hu (by simpa using List.mem_cons_of_mem x hmem) hdvd
        simp [primecoreStep, hdiv, ih hex' hu']

private lemma primecoreStep_perm_program
    {n : ℕ} (encode : Fin n ↪ Nat) (hPrime : ∀ i, Nat.Prime (encode i))
    (σ : Equiv.Perm (Fin n)) (i : Fin n) :
    primecoreStep ((List.finRange n).map fun j => (encode (σ j), encode j)) (encode i) =
      encode (σ i) := by
  let Fσ := (List.finRange n).map fun j => (encode (σ j), encode j)
  have hex : ∃ instr ∈ Fσ, instr.2 ∣ encode i := by
    refine ⟨(encode (σ i), encode i), ?_, dvd_rfl⟩
    apply List.mem_map.mpr
    exact ⟨i, by simp, by simp⟩
  refine primecoreStep_eq_of_exists_unique hex ?_
  intro a' d' hmem hdvd
  rcases List.mem_map.mp hmem with ⟨j, -, hEq⟩
  cases hEq
  have hEqOrOne := (Nat.dvd_prime (hPrime i)).mp hdvd
  rcases hEqOrOne with hOne | hEq
  · exact False.elim ((hPrime j).ne_one hOne)
  · have hj : j = i := encode.injective hEq
    subst j
    simp [Nat.div_self (hPrime i).pos]

/-- Finite permutations admit a prime-encoded FRACTRAN realization, and any program carrying a
prime support of size `n` needs at least `n` instructions covering those denominators.
    thm:pom-fractran-permutation-embedding-length -/
theorem paper_pom_fractran_permutation_embedding_length (n : ℕ) :
    ∃ encode : Fin n ↪ Nat, ∃ compile : Equiv.Perm (Fin n) → List (Nat × Nat),
      (∀ i, Nat.Prime (encode i)) ∧
        Function.Injective
          (fun σ : Equiv.Perm (Fin n) => fun i : Fin n => primecoreStep (compile σ) (encode i)) ∧
        (∀ σ τ i, primecoreStep (compile (σ * τ)) (encode i) =
          primecoreStep (compile σ) (primecoreStep (compile τ) (encode i))) ∧
        (∀ σ i, primecoreStep (compile σ) (encode i) = encode (σ i)) ∧
        (∀ σ, (compile σ).length = n) ∧
        (∀ F : List (Nat × Nat),
          (∀ instr ∈ F, instr.2 ≠ 1) →
          (∀ i : Fin n, ∃ instr ∈ F, instr.2 ∣ encode i) →
          n ≤ F.length) := by
  classical
  let e : Fin n ≃ Fin n := Equiv.refl _
  let encode : Fin n ↪ Nat := {
    toFun := fun i => Nat.nth Nat.Prime (e i)
    inj' := by
      intro i j hij
      apply e.injective
      exact Fin.ext <| (Nat.nth_strictMono Nat.infinite_setOf_prime).injective hij
  }
  have hPrime : ∀ i, Nat.Prime (encode i) := by
    intro i
    simpa [encode] using Nat.prime_nth_prime (e i)
  let compile : Equiv.Perm (Fin n) → List (Nat × Nat) :=
    fun σ => (List.finRange n).map fun i => (encode (σ i), encode i)
  refine ⟨encode, compile, hPrime, ?_, ?_, ?_, ?_, ?_⟩
  · intro σ τ hστ
    ext i
    have hfin : σ i = τ i := by
      apply encode.injective
      have hEval := congrFun hστ i
      simpa [compile, primecoreStep_perm_program, hPrime] using hEval
    exact congrArg Fin.val hfin
  · intro σ τ i
    rw [primecoreStep_perm_program encode hPrime τ i, primecoreStep_perm_program encode hPrime σ (τ i)]
    simpa [compile] using (primecoreStep_perm_program encode hPrime (σ * τ) i)
  · intro σ i
    exact primecoreStep_perm_program encode hPrime σ i
  · intro σ
    simp [compile]
  · intro F hnonunit hcover
    let denoms : Finset Nat := (F.map Prod.snd).toFinset
    let encoded : Finset Nat := Finset.univ.image encode
    have hsubset : encoded ⊆ denoms := by
      intro x hx
      rcases Finset.mem_image.mp hx with ⟨i, -, rfl⟩
      rcases hcover i with ⟨instr, hinstr, hdiv⟩
      have hEqOrOne := (Nat.dvd_prime (hPrime i)).mp hdiv
      rcases hEqOrOne with hOne | hEq
      · exact (hnonunit instr hinstr hOne).elim
      · rw [← hEq]
        exact List.mem_toFinset.mpr <| List.mem_map.mpr ⟨instr, hinstr, rfl⟩
    have hcardEncoded : encoded.card = n := by
      simpa [encoded] using Finset.card_image_of_injective (s := Finset.univ) encode.injective
    calc
      n = encoded.card := hcardEncoded.symm
      _ ≤ denoms.card := Finset.card_le_card hsubset
      _ ≤ F.length := by
        simpa [denoms] using List.toFinset_card_le (F.map Prod.snd)

end Omega.POM
