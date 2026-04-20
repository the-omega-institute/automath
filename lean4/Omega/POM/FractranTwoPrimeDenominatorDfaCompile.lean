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

/-- Sparse local compiler for a partially defined Turing-step table: the denominator still encodes
exactly one `(state, symbol)` pair, while the numerator additionally records the move prime. -/
theorem paper_pom_fractran_tm_local_compile_prime_sparse
    (Q Sigma : Type) [Fintype Q] [DecidableEq Q] [Fintype Sigma] [DecidableEq Sigma]
    (delta : Q → Sigma → Option (Q × Sigma × Fin 3)) :
    ∃ (encodeQ : Q ↪ Nat) (encodeSigma : Sigma ↪ Nat) (encodeMove : Fin 3 ↪ Nat)
      (F : List (Nat × Nat)),
      (∀ q, Nat.Prime (encodeQ q)) ∧
      (∀ a, Nat.Prime (encodeSigma a)) ∧
      (∀ mv, Nat.Prime (encodeMove mv)) ∧
      Disjoint (Set.range encodeQ) (Set.range encodeSigma) ∧
      Disjoint (Set.range encodeQ) (Set.range encodeMove) ∧
      Disjoint (Set.range encodeSigma) (Set.range encodeMove) ∧
      (∀ q a q' a' mv, delta q a = some (q', a', mv) →
        primecoreStep F (encodeQ q * encodeSigma a) =
          encodeQ q' * encodeSigma a' * encodeMove mv) := by
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
    toFun := fun a => Nat.nth Nat.Prime (Fintype.card Q + eSigma a)
    inj' := by
      intro a₁ a₂ h
      apply eSigma.injective
      exact Fin.ext <| Nat.add_left_cancel <|
        (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h
  }
  let encodeMove : Fin 3 ↪ Nat := {
    toFun := fun mv => Nat.nth Nat.Prime (Fintype.card Q + Fintype.card Sigma + mv)
    inj' := by
      intro mv₁ mv₂ h
      have h' :
          Nat.nth Nat.Prime (Fintype.card Q + (Fintype.card Sigma + mv₁)) =
            Nat.nth Nat.Prime (Fintype.card Q + (Fintype.card Sigma + mv₂)) := by
        simpa [Nat.add_assoc] using h
      exact Fin.ext <| Nat.add_left_cancel <| Nat.add_left_cancel <|
        (Nat.nth_strictMono Nat.infinite_setOf_prime).injective h'
  }
  let pairList : List (Q × Sigma) :=
    (Finset.univ : Finset Q).toList.product (Finset.univ : Finset Sigma).toList
  let F : List (Nat × Nat) :=
    pairList.map fun qs =>
      match delta qs.1 qs.2 with
      | some (q', a', mv) =>
          (encodeQ q' * encodeSigma a' * encodeMove mv, encodeQ qs.1 * encodeSigma qs.2)
      | none => (1, encodeQ qs.1 * encodeSigma qs.2)
  have hPrimeQ : ∀ q, Nat.Prime (encodeQ q) := by
    intro q
    simpa [encodeQ] using Nat.prime_nth_prime (eQ q)
  have hPrimeSigma : ∀ a, Nat.Prime (encodeSigma a) := by
    intro a
    simpa [encodeSigma] using Nat.prime_nth_prime (Fintype.card Q + eSigma a)
  have hPrimeMove : ∀ mv, Nat.Prime (encodeMove mv) := by
    intro mv
    simpa [encodeMove, Nat.add_assoc] using
      Nat.prime_nth_prime (Fintype.card Q + Fintype.card Sigma + mv)
  have hDisjointQS : Disjoint (Set.range encodeQ) (Set.range encodeSigma) := by
    refine Set.disjoint_left.2 ?_
    intro x hxQ hxSigma
    rcases hxQ with ⟨q, rfl⟩
    rcases hxSigma with ⟨a, ha⟩
    have hidx : (eQ q : Nat) = Fintype.card Q + (eSigma a : Nat) := by
      apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
      simpa [encodeQ, encodeSigma] using ha.symm
    omega
  have hDisjointQM : Disjoint (Set.range encodeQ) (Set.range encodeMove) := by
    refine Set.disjoint_left.2 ?_
    intro x hxQ hxMove
    rcases hxQ with ⟨q, rfl⟩
    rcases hxMove with ⟨mv, hmv⟩
    have hidx : (eQ q : Nat) = Fintype.card Q + Fintype.card Sigma + (mv : Nat) := by
      apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
      simpa [encodeQ, encodeMove, Nat.add_assoc] using hmv.symm
    omega
  have hDisjointSM : Disjoint (Set.range encodeSigma) (Set.range encodeMove) := by
    refine Set.disjoint_left.2 ?_
    intro x hxSigma hxMove
    rcases hxSigma with ⟨a, rfl⟩
    rcases hxMove with ⟨mv, hmv⟩
    have hidx : Fintype.card Q + (eSigma a : Nat) =
        Fintype.card Q + Fintype.card Sigma + (mv : Nat) := by
      apply (Nat.nth_strictMono Nat.infinite_setOf_prime).injective
      simpa [encodeSigma, encodeMove, Nat.add_assoc] using hmv.symm
    omega
  refine ⟨encodeQ, encodeSigma, encodeMove, F, hPrimeQ, hPrimeSigma, hPrimeMove,
    hDisjointQS, hDisjointQM, hDisjointSM, ?_⟩
  intro q a q' a' mv hdelta
  have hExists :
      ∃ instr ∈ F, instr.2 ∣ encodeQ q * encodeSigma a := by
    refine ⟨(encodeQ q' * encodeSigma a' * encodeMove mv, encodeQ q * encodeSigma a), ?_,
      dvd_rfl⟩
    apply List.mem_map.mpr
    refine ⟨(q, a), ?_, ?_⟩
    · simp [pairList]
    · simp [hdelta]
  refine primecoreStep_eq_of_exists_unique hExists ?_
  intro num den hmem hdvd
  have hmem' :
      ∃ q₀ a₀,
        num = (match delta q₀ a₀ with
          | some (q₁, a₁, mv₁) => encodeQ q₁ * encodeSigma a₁ * encodeMove mv₁
          | none => 1) ∧
        den = encodeQ q₀ * encodeSigma a₀ := by
    rcases List.mem_map.mp hmem with ⟨qs, hqs, hEq⟩
    rcases qs with ⟨q₀, a₀⟩
    cases hdelta₀ : delta q₀ a₀ with
    | none =>
        refine ⟨q₀, a₀, ?_, ?_⟩
        · simpa [hdelta₀] using (congrArg Prod.fst hEq).symm
        · simpa [hdelta₀] using (congrArg Prod.snd hEq).symm
    | some out =>
        rcases out with ⟨q₁, a₁, mv₁⟩
        refine ⟨q₀, a₀, ?_, ?_⟩
        · simpa [hdelta₀] using (congrArg Prod.fst hEq).symm
        · simpa [hdelta₀] using (congrArg Prod.snd hEq).symm
  rcases hmem' with ⟨q₀, a₀, hnum, hden⟩
  subst num den
  have hqdvd : encodeQ q₀ ∣ encodeQ q * encodeSigma a := by
    exact dvd_trans (dvd_mul_of_dvd_left (dvd_refl (encodeQ q₀)) _) hdvd
  have hSigmaDvd : encodeSigma a₀ ∣ encodeQ q * encodeSigma a := by
    exact dvd_trans (dvd_mul_of_dvd_right (dvd_refl (encodeSigma a₀)) _) hdvd
  have hqeqVal : encodeQ q₀ = encodeQ q := by
    rcases (hPrimeQ q₀).dvd_mul.mp hqdvd with hq | hcross
    · exact (Nat.prime_dvd_prime_iff_eq (hPrimeQ q₀) (hPrimeQ q)).mp hq
    · have hEqCross : encodeQ q₀ = encodeSigma a :=
        (Nat.prime_dvd_prime_iff_eq (hPrimeQ q₀) (hPrimeSigma a)).mp hcross
      have hRangeQ : encodeQ q₀ ∈ Set.range encodeQ := ⟨q₀, rfl⟩
      have hRangeSigma : encodeQ q₀ ∈ Set.range encodeSigma := by
        rw [hEqCross]
        exact ⟨a, rfl⟩
      exact False.elim ((Set.disjoint_left.mp hDisjointQS) hRangeQ hRangeSigma)
  have hSigmaEqVal : encodeSigma a₀ = encodeSigma a := by
    rcases (hPrimeSigma a₀).dvd_mul.mp hSigmaDvd with hcross | ha
    · have hEqCross : encodeSigma a₀ = encodeQ q :=
        (Nat.prime_dvd_prime_iff_eq (hPrimeSigma a₀) (hPrimeQ q)).mp hcross
      have hRangeQ : encodeSigma a₀ ∈ Set.range encodeQ := by
        rw [hEqCross]
        exact ⟨q, rfl⟩
      have hRangeSigma : encodeSigma a₀ ∈ Set.range encodeSigma := ⟨a₀, rfl⟩
      exact False.elim ((Set.disjoint_left.mp hDisjointQS) hRangeQ hRangeSigma)
    · exact (Nat.prime_dvd_prime_iff_eq (hPrimeSigma a₀) (hPrimeSigma a)).mp ha
  have hqeq : q₀ = q := encodeQ.injective hqeqVal
  have hSigmaEq : a₀ = a := encodeSigma.injective hSigmaEqVal
  subst q₀ a₀
  have hpos : 0 < encodeQ q * encodeSigma a := Nat.mul_pos (hPrimeQ q).pos (hPrimeSigma a).pos
  have hdivself : (encodeQ q * encodeSigma a) / (encodeQ q * encodeSigma a) = 1 :=
    Nat.div_self hpos
  simp [hdelta, hdivself]

end Omega.POM
