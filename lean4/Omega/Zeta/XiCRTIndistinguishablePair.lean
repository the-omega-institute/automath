import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

namespace Omega.Zeta

/-- Prime multiplicity across a list of localization supports. -/
def xiPrimeSupportMultiplicity : List (Finset Nat) → Nat → Nat
  | [], _ => 0
  | S :: supports, p => (if p ∈ S then 1 else 0) + xiPrimeSupportMultiplicity supports p

/-- Prime-by-prime finite-shadow multiplicity: only primes dividing `n` contribute. -/
def xiListShadowMultiplicity (supports : List (Finset Nat)) (n p : Nat) : Nat :=
  if p ∈ n.factorization.support then xiPrimeSupportMultiplicity supports p else 0

/-- Joint prime count for a target support `T`: detect whether `T` appears as one full summand. -/
def xiJointPrimeCount (supports : List (Finset Nat)) (T : Finset Nat) : Nat :=
  if T ∈ supports then 1 else 0

private lemma empty_supports_multiplicity (n p : Nat) :
    xiPrimeSupportMultiplicity (List.replicate n (∅ : Finset Nat)) p = 0 := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [List.replicate, xiPrimeSupportMultiplicity, ih]

private lemma singleton_supports_multiplicity (l : List Nat) (hl : l.Nodup) (p : Nat) :
    xiPrimeSupportMultiplicity (l.map fun q => ({q} : Finset Nat)) p = if p ∈ l then 1 else 0 := by
  induction l generalizing p with
  | nil =>
      simp [xiPrimeSupportMultiplicity]
  | cons a l ih =>
      rcases List.nodup_cons.mp hl with ⟨ha, hl'⟩
      by_cases hp : p = a
      · subst hp
        have htail : xiPrimeSupportMultiplicity (l.map fun q => ({q} : Finset Nat)) p = 0 := by
          simpa [ha] using ih hl' p
        simpa [xiPrimeSupportMultiplicity, List.mem_cons, ha] using htail
      · simpa [xiPrimeSupportMultiplicity, List.mem_cons, hp] using ih hl' p

private lemma concentrated_supports_multiplicity (T : Finset Nat) (n p : Nat) :
    xiPrimeSupportMultiplicity (T :: List.replicate n (∅ : Finset Nat)) p = if p ∈ T then 1 else 0 := by
  simp [xiPrimeSupportMultiplicity, empty_supports_multiplicity]

private lemma target_not_mem_singleton_supports (l : List Nat) (T : Finset Nat) (hT : 2 ≤ T.card) :
    T ∉ l.map (fun p => ({p} : Finset Nat)) := by
  intro hmem
  induction l with
  | nil =>
      simp at hmem
  | cons a l ih =>
      simp only [List.map_cons, List.mem_cons] at hmem
      rcases hmem with hEq | hmem
      · have hcardEq : ({a} : Finset Nat).card = T.card := by simp [hEq]
        simp at hcardEq
        omega
      · exact ih hmem

/-- The singleton list model `AT` and the concentrated model `AT'` have the same prime-by-prime
finite-shadow multiplicities, but their joint counts on `T` differ.
    cor:xi-crt-indistinguishable-pair -/
theorem paper_xi_crt_indistinguishable_pair (T : Finset Nat) (hT : 2 ≤ T.card)
    (hprime : ∀ p ∈ T, Nat.Prime p) :
    let AT : List (Finset Nat) := T.toList.map (fun p => ({p} : Finset Nat))
    let AT' : List (Finset Nat) := T :: List.replicate (T.card - 1) (∅ : Finset Nat)
    (∀ n p : Nat, xiListShadowMultiplicity AT n p = xiListShadowMultiplicity AT' n p) ∧
      xiJointPrimeCount AT T = 0 ∧ xiJointPrimeCount AT' T = 1 := by
  let _ := hprime
  dsimp
  have hmult :
      ∀ p : Nat,
        xiPrimeSupportMultiplicity (T.toList.map (fun q => ({q} : Finset Nat))) p =
          xiPrimeSupportMultiplicity (T :: List.replicate (T.card - 1) (∅ : Finset Nat)) p := by
    intro p
    rw [singleton_supports_multiplicity T.toList T.nodup_toList, concentrated_supports_multiplicity]
    simp
  have hTne : T ≠ ∅ := by
    intro h
    simp [h] at hT
  have hnotmem : T ∉ T.toList.map (fun p => ({p} : Finset Nat)) :=
    target_not_mem_singleton_supports T.toList T hT
  refine ⟨?_, ?_, ?_⟩
  · intro n p
    by_cases hfac : Nat.Prime p ∧ p ∣ n ∧ n ≠ 0
    · have hp : p ∈ n.factorization.support := by
        simpa [Nat.support_factorization, Nat.mem_primeFactors, and_assoc] using hfac
      rw [xiListShadowMultiplicity, xiListShadowMultiplicity, if_pos hp, if_pos hp]
      exact hmult p
    · have hp : p ∉ n.factorization.support := by
        simpa [Nat.support_factorization, Nat.mem_primeFactors, and_assoc] using hfac
      rw [xiListShadowMultiplicity, xiListShadowMultiplicity, if_neg hp, if_neg hp]
  · simp [xiJointPrimeCount, hnotmem]
  · simp [xiJointPrimeCount]

end Omega.Zeta
