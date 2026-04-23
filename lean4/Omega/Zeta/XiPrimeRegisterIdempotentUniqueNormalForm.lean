import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Tactic
import Omega.Zeta.PrimeRegisterIdempotentExactCount

namespace Omega.Zeta

/-- Fixed-point set of a finite endomorphism. -/
def xi_prime_register_idempotent_unique_normal_form_fixedPoints {n : ℕ} (f : Fin n → Fin n) :
    Finset (Fin n) :=
  Finset.univ.filter fun i => f i = i

/-- Evaluation of the normal form attached to a fixed-point set `F` and a complement-to-`F` map
`φ`. -/
def xi_prime_register_idempotent_unique_normal_form_eval {n : ℕ} (F : Finset (Fin n))
    (φ : { i : Fin n // i ∉ F } → F) (i : Fin n) : Fin n :=
  if h : i ∈ F then i else (φ ⟨i, h⟩ : F)

/-- Canonical complement-to-fixed-set map attached to an idempotent endomorphism. -/
def xi_prime_register_idempotent_unique_normal_form_canonicalMap {n : ℕ} (f : Fin n → Fin n)
    (hf : ∀ i, f (f i) = f i) :
    { i : Fin n // i ∉ xi_prime_register_idempotent_unique_normal_form_fixedPoints f } →
      xi_prime_register_idempotent_unique_normal_form_fixedPoints f :=
  fun i =>
    ⟨f i.1, by
      simp [xi_prime_register_idempotent_unique_normal_form_fixedPoints, hf (i.1)]⟩

theorem xi_prime_register_idempotent_unique_normal_form_fixedPoints_spec {n : ℕ}
    (f : Fin n → Fin n) (i : Fin n) :
    i ∈ xi_prime_register_idempotent_unique_normal_form_fixedPoints f ↔ f i = i := by
  simp [xi_prime_register_idempotent_unique_normal_form_fixedPoints]

theorem xi_prime_register_idempotent_unique_normal_form_canonical_eval {n : ℕ}
    (f : Fin n → Fin n) (hf : ∀ i, f (f i) = f i) :
    ∀ i,
      f i =
        xi_prime_register_idempotent_unique_normal_form_eval
          (xi_prime_register_idempotent_unique_normal_form_fixedPoints f)
          (xi_prime_register_idempotent_unique_normal_form_canonicalMap f hf) i := by
  intro i
  by_cases hi : i ∈ xi_prime_register_idempotent_unique_normal_form_fixedPoints f
  · have hfix : f i = i := by
      simpa [xi_prime_register_idempotent_unique_normal_form_fixedPoints] using hi
    simp [xi_prime_register_idempotent_unique_normal_form_eval, hi, hfix]
  · simp [xi_prime_register_idempotent_unique_normal_form_eval, hi,
      xi_prime_register_idempotent_unique_normal_form_canonicalMap]

theorem xi_prime_register_idempotent_unique_normal_form_function_count {n k : ℕ}
    (F : Finset (Fin n)) (hk : F.card = k) :
    Fintype.card ({ i : Fin n // i ∉ F } → F) = k ^ (n - k) := by
  have hcardF : Fintype.card F = k := by
    simpa [hk] using Fintype.card_coe F
  have hcardCompl : Fintype.card { i : Fin n // i ∉ F } = n - k := by
    calc
      Fintype.card { i : Fin n // i ∉ F } =
          Fintype.card (Fin n) - Fintype.card { i : Fin n // i ∈ F } := by
            simpa using Fintype.card_subtype_compl (fun i : Fin n => i ∈ F)
      _ = n - F.card := by simp
      _ = n - k := by simpa [hk]
  calc
    Fintype.card ({ i : Fin n // i ∉ F } → F) =
        Fintype.card F ^ Fintype.card { i : Fin n // i ∉ F } := by
          simp
    _ = k ^ (n - k) := by rw [hcardF, hcardCompl]

/-- Paper label: `thm:xi-prime-register-idempotent-unique-normal-form`. Idempotent endomorphisms of
`Fin n` are determined by their fixed-point set and the induced map from its complement into that
fixed-point set; the complement map has exactly `k^(n-k)` choices when the fixed set has cardinality
`k`, and summing over `k` recovers the standard prime-register idempotent count. -/
theorem paper_xi_prime_register_idempotent_unique_normal_form (n : Nat) :
    (∀ f : Fin n → Fin n, (∀ i, f (f i) = f i) →
      let F := xi_prime_register_idempotent_unique_normal_form_fixedPoints f
      (∃! G : Finset (Fin n), ∀ i, i ∈ G ↔ f i = i) ∧
        (∃! φ : { i : Fin n // i ∉ F } → F,
          ∀ i, f i = xi_prime_register_idempotent_unique_normal_form_eval F φ i) ∧
        (∀ k, F.card = k → Fintype.card ({ i : Fin n // i ∉ F } → F) = k ^ (n - k))) ∧
      (∀ k, primeRegisterIdempotentCount n k = Nat.choose n k * k ^ (n - k)) ∧
      primeRegisterIdempotentTotalCount n =
        ∑ k ∈ Finset.Icc 1 n, Nat.choose n k * k ^ (n - k) := by
  refine ⟨?_, ?_, ?_⟩
  · intro f hf
    dsimp
    let F := xi_prime_register_idempotent_unique_normal_form_fixedPoints f
    refine ⟨?_, ?_, ?_⟩
    · refine ⟨F, ?_, ?_⟩
      · intro i
        simpa [F] using xi_prime_register_idempotent_unique_normal_form_fixedPoints_spec f i
      · intro G hG
        ext i
        calc
          i ∈ G ↔ f i = i := hG i
          _ ↔ i ∈ F := by
            simpa [F] using (xi_prime_register_idempotent_unique_normal_form_fixedPoints_spec f i).symm
    · refine ⟨xi_prime_register_idempotent_unique_normal_form_canonicalMap f hf, ?_, ?_⟩
      · intro i
        simpa [F] using xi_prime_register_idempotent_unique_normal_form_canonical_eval f hf i
      · intro φ hφ
        funext i
        apply Subtype.ext
        have hφi : ((φ i : F) : Fin n) = f i.1 := by
          simpa [xi_prime_register_idempotent_unique_normal_form_eval, i.2] using (hφ i.1).symm
        have hcanon :
            (((xi_prime_register_idempotent_unique_normal_form_canonicalMap f hf) i : F) : Fin n) =
              f i.1 := by
          rfl
        exact hφi.trans hcanon.symm
    · intro k hk
      simpa [F] using
        xi_prime_register_idempotent_unique_normal_form_function_count
          (xi_prime_register_idempotent_unique_normal_form_fixedPoints f) hk
  · intro k
    rfl
  · simp [primeRegisterIdempotentTotalCount, primeRegisterIdempotentCount]

end Omega.Zeta
