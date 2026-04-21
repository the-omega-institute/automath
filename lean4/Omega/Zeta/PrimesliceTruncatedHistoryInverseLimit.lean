import Mathlib
import Omega.Zeta.XiPrimeRegisterHistoryInverseLimit

open scoped BigOperators

namespace Omega.Zeta

noncomputable section

/-- Prime-power code for a finite history layer: the `i`-th coordinate lives on the `p i` slice. -/
def xiPrimesliceDigitsCode (p : ℕ → ℕ) {k : ℕ} (a : Fin k → ℕ) : ℕ :=
  ∏ i : Fin k, p i ^ (a i + 1)

/-- The layer encoding keeps the visible state and replaces the history by its prime-slice code. -/
def xiPrimesliceEncode {X : Type*} (p : ℕ → ℕ) (k : ℕ) :
    XiPrimeRegisterLayer X k → X × ℕ
  | (x, a) => (x, xiPrimesliceDigitsCode p a)

/-- Removing the deepest layer drops the last prime slice. -/
def xiPrimesliceTail {k : ℕ} (a : Fin (k + 1) → ℕ) : Fin k → ℕ :=
  fun i => a i.castSucc

/-- Factorization profile of the prime-slice code. -/
noncomputable def xiPrimesliceFactorization (p : ℕ → ℕ) {k : ℕ} (a : Fin k → ℕ) : ℕ →₀ ℕ :=
  ∑ i : Fin k, Finsupp.single (p i) (a i + 1)

@[simp] lemma xiPrimesliceFactorization_apply (p : ℕ → ℕ) {k : ℕ}
    (hinj : Function.Injective p) (a : Fin k → ℕ) (i : Fin k) :
    xiPrimesliceFactorization p a (p i) = a i + 1 := by
  classical
  unfold xiPrimesliceFactorization
  have h :
      (∑ x : Fin k, (Finsupp.single (p x) (a x + 1)) (p i)) = a i + 1 := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hji
      have hpji : p j ≠ p i := by
        intro hpi
        exact hji (Fin.ext (hinj hpi))
      simp [hpji]
    · intro hi
      simp at hi
  simpa using h

lemma xiPrimesliceDigitsCode_factorization (p : ℕ → ℕ) {k : ℕ}
    (hprime : ∀ n, Nat.Prime (p n)) (a : Fin k → ℕ) :
    (xiPrimesliceDigitsCode p a).factorization = xiPrimesliceFactorization p a := by
  classical
  unfold xiPrimesliceDigitsCode xiPrimesliceFactorization
  rw [Nat.factorization_prod]
  · refine Finset.sum_congr rfl ?_
    intro i hi
    simpa using Nat.Prime.factorization_pow (hprime i) (k := a i + 1)
  · intro i hi
    exact pow_ne_zero _ (Nat.Prime.ne_zero (hprime i))

lemma xiPrimesliceDigitsCode_injective (p : ℕ → ℕ) {k : ℕ}
    (hprime : ∀ n, Nat.Prime (p n)) (hinj : Function.Injective p) :
    Function.Injective (xiPrimesliceDigitsCode p (k := k)) := by
  intro a b hab
  have hfac :
      xiPrimesliceFactorization p a = xiPrimesliceFactorization p b := by
    calc
      xiPrimesliceFactorization p a = (xiPrimesliceDigitsCode p a).factorization := by
        symm
        exact xiPrimesliceDigitsCode_factorization p hprime a
      _ = (xiPrimesliceDigitsCode p b).factorization := by rw [hab]
      _ = xiPrimesliceFactorization p b := xiPrimesliceDigitsCode_factorization p hprime b
  funext i
  have hi := congrArg (fun f => f (p i)) hfac
  exact Nat.succ.inj <| by
    simpa [Nat.succ_eq_add_one, xiPrimesliceFactorization_apply, hinj] using hi

lemma xiPrimesliceEncode_injective {X : Type*} (p : ℕ → ℕ) (k : ℕ)
    (hprime : ∀ n, Nat.Prime (p n)) (hinj : Function.Injective p) :
    Function.Injective (xiPrimesliceEncode (X := X) p k) := by
  intro a b hab
  rcases a with ⟨x, aa⟩
  rcases b with ⟨y, bb⟩
  have hx : x = y := congrArg Prod.fst hab
  have hcode : xiPrimesliceDigitsCode p aa = xiPrimesliceDigitsCode p bb := congrArg Prod.snd hab
  cases hx
  exact Prod.ext rfl (xiPrimesliceDigitsCode_injective p hprime hinj hcode)

lemma xiPrimesliceDigitsCode_succ (p : ℕ → ℕ) {k : ℕ} (a : Fin (k + 1) → ℕ) :
    xiPrimesliceDigitsCode p a =
      xiPrimesliceDigitsCode p (xiPrimesliceTail a) * p (Fin.last k) ^ (a (Fin.last k) + 1) := by
  unfold xiPrimesliceDigitsCode xiPrimesliceTail
  simpa using (Fin.prod_univ_castSucc fun i : Fin (k + 1) => p i ^ (a i + 1))

/-- Paper label: `thm:xi-time-part53ac-primeslice-truncated-history-inverse-limit`.
The prime-slice multiplicative code is injective at every finite depth, truncation removes the
deepest prime slice, and the compatible tower is equivalent to the branch-register inverse limit. -/
theorem paper_xi_time_part53ac_primeslice_truncated_history_inverse_limit
    (X : Type*) (p : ℕ → ℕ)
    (hprime : ∀ n, Nat.Prime (p n)) (hinj : Function.Injective p) :
    (∀ k : ℕ, Function.Injective (xiPrimesliceEncode (X := X) p k)) ∧
      (∀ k : ℕ, ∀ a : Fin (k + 1) → ℕ,
        xiPrimesliceDigitsCode p a =
          xiPrimesliceDigitsCode p (xiPrimesliceTail a) *
            p (Fin.last k) ^ (a (Fin.last k) + 1)) ∧
      Nonempty (XiPrimeRegisterCompatibleFamily X ≃ XiPrimeRegisterStream X) := by
  refine ⟨fun k => xiPrimesliceEncode_injective (X := X) p k hprime hinj, ?_, ?_⟩
  · intro k a
    exact xiPrimesliceDigitsCode_succ p a
  · exact ⟨xiPrimeRegisterInverseLimitEquiv X⟩

end

end Omega.Zeta
