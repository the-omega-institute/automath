import Mathlib.NumberTheory.PrimeCounting
import Mathlib.Tactic

namespace Omega.POM

/-- First-fit FRACTRAN-style step: scan the instruction list and apply the first denominator that
divides the input. -/
def primecoreStep : List (Nat × Nat) → Nat → Nat
  | [], n => n
  | (a, d) :: F, n => if d ∣ n then a * (n / d) else primecoreStep F n

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

/-- Two disjoint prime alphabets compile a DFA transition table into a single FRACTRAN step
table with one denominator per state-symbol pair. -/
theorem paper_pom_fractran_two_prime_denominator_dfa_compile
    (Q Sigma : Type) [Fintype Q] [DecidableEq Q] [Fintype Sigma] [DecidableEq Sigma]
    (delta : Q -> Sigma -> Q) :
    ∃ (encodeQ : Q ↪ Nat) (encodeSigma : Sigma ↪ Nat) (F : List (Nat × Nat)),
      (∀ q, Nat.Prime (encodeQ q)) ∧
      (∀ s, Nat.Prime (encodeSigma s)) ∧
      Disjoint (Set.range encodeQ) (Set.range encodeSigma) ∧
      (∀ q s, primecoreStep F (encodeQ q * encodeSigma s) = encodeQ (delta q s)) := by
  classical
  let eQ : Q ≃ Fin (Fintype.card Q) := Fintype.equivFin Q
  let eSigma : Sigma ≃ Fin (Fintype.card Sigma) := Fintype.equivFin Sigma
  let encodeQ : Q ↪ Nat := {
    toFun := fun q => Nat.nth Nat.Prime (eQ q)
    inj' := by
      intro q₁ q₂ h
      apply eQ.injective
      exact Fin.ext <| (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
  }
  let encodeSigma : Sigma ↪ Nat := {
    toFun := fun s => Nat.nth Nat.Prime (Fintype.card Q + eSigma s)
    inj' := by
      intro s₁ s₂ h
      apply eSigma.injective
      exact Fin.ext <| Nat.add_left_cancel <|
        (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
  }
  let pairList : List (Q × Sigma) :=
    (Finset.univ : Finset Q).toList.product (Finset.univ : Finset Sigma).toList
  let F : List (Nat × Nat) :=
    pairList.map fun qs => (encodeQ (delta qs.1 qs.2), encodeQ qs.1 * encodeSigma qs.2)
  have hPrimeQ : ∀ q, Nat.Prime (encodeQ q) := by
    intro q
    simpa [encodeQ] using Nat.prime_nth_prime (eQ q)
  have hPrimeSigma : ∀ s, Nat.Prime (encodeSigma s) := by
    intro s
    simpa [encodeSigma] using Nat.prime_nth_prime (Fintype.card Q + eSigma s)
  have hDisjoint : Disjoint (Set.range encodeQ) (Set.range encodeSigma) := by
    refine Set.disjoint_left.2 ?_
    intro x hxQ hxSigma
    rcases hxQ with ⟨q, rfl⟩
    rcases hxSigma with ⟨s, hs⟩
    have hidx : (eQ q : Nat) = Fintype.card Q + (eSigma s : Nat) := by
      apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
      simpa [encodeQ, encodeSigma] using hs.symm
    omega
  refine ⟨encodeQ, encodeSigma, F, hPrimeQ, hPrimeSigma, hDisjoint, ?_⟩
  intro q s
  have hExists :
      ∃ instr ∈ F, instr.2 ∣ encodeQ q * encodeSigma s := by
    refine ⟨(encodeQ (delta q s), encodeQ q * encodeSigma s), ?_, dvd_rfl⟩
    apply List.mem_map.mpr
    refine ⟨(q, s), ?_, by simp⟩
    simp [pairList]
  refine primecoreStep_eq_of_exists_unique hExists ?_
  intro a' d' hmem hdvd
  have hmem' :
      ∃ q' s', a' = encodeQ (delta q' s') ∧ d' = encodeQ q' * encodeSigma s' := by
    rcases List.mem_map.mp hmem with ⟨qs, hqs, hEq⟩
    rcases qs with ⟨q', s'⟩
    refine ⟨q', s', ?_, ?_⟩
    · simpa using (congrArg Prod.fst hEq).symm
    · simpa using (congrArg Prod.snd hEq).symm
  rcases hmem' with ⟨q', s', rfl, rfl⟩
  have hqdvd : encodeQ q' ∣ encodeQ q * encodeSigma s := by
    exact dvd_trans (dvd_mul_of_dvd_left (dvd_refl (encodeQ q')) _) hdvd
  have hsigmadvd : encodeSigma s' ∣ encodeQ q * encodeSigma s := by
    exact dvd_trans (dvd_mul_of_dvd_right (dvd_refl (encodeSigma s')) _) hdvd
  have hqeqVal : encodeQ q' = encodeQ q := by
    rcases (hPrimeQ q').dvd_mul.mp hqdvd with hq | hcross
    · exact (Nat.prime_dvd_prime_iff_eq (hPrimeQ q') (hPrimeQ q)).mp hq
    · have hEq : encodeQ q' = encodeSigma s :=
        (Nat.prime_dvd_prime_iff_eq (hPrimeQ q') (hPrimeSigma s)).mp hcross
      have hRangeQ : encodeQ q' ∈ Set.range encodeQ := ⟨q', rfl⟩
      have hRangeSigma : encodeQ q' ∈ Set.range encodeSigma := by
        rw [hEq]
        exact ⟨s, rfl⟩
      exact False.elim ((Set.disjoint_left.mp hDisjoint) hRangeQ hRangeSigma)
  have hsigmaEqVal : encodeSigma s' = encodeSigma s := by
    rcases (hPrimeSigma s').dvd_mul.mp hsigmadvd with hcross | hs
    · have hEq : encodeSigma s' = encodeQ q :=
        (Nat.prime_dvd_prime_iff_eq (hPrimeSigma s') (hPrimeQ q)).mp hcross
      have hRangeQ : encodeSigma s' ∈ Set.range encodeQ := by
        rw [hEq]
        exact ⟨q, rfl⟩
      have hRangeSigma : encodeSigma s' ∈ Set.range encodeSigma := ⟨s', rfl⟩
      exact False.elim ((Set.disjoint_left.mp hDisjoint) hRangeQ hRangeSigma)
    · exact (Nat.prime_dvd_prime_iff_eq (hPrimeSigma s') (hPrimeSigma s)).mp hs
  have hqeq : q' = q := encodeQ.injective hqeqVal
  have hsigmaEq : s' = s := encodeSigma.injective hsigmaEqVal
  have hpos : 0 < encodeQ q * encodeSigma s := Nat.mul_pos (hPrimeQ q).pos (hPrimeSigma s).pos
  have hdivself : (encodeQ q * encodeSigma s) / (encodeQ q * encodeSigma s) = 1 := Nat.div_self hpos
  simp [hqeq, hsigmaEq, hdivself]

end Omega.POM
