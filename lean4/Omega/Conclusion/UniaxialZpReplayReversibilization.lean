import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Tactic

namespace Omega.Conclusion

private noncomputable def conclusion_uniaxial_zp_replay_reversibilization_symbolEmbedding
    {S : Type*} [Fintype S]
    {p : ℕ} (hcard : Fintype.card S ≤ p) : S ↪ Fin p where
  toFun s := Fin.castLE hcard (Fintype.equivFin S s)
  inj' := Fin.castLE_injective hcard |>.comp (Fintype.equivFin S).injective

/-- A finite-state replay trace can be encoded digitwise in one prime alphabet: choose a prime
larger than the finite trace alphabet, embed each trace symbol into `Fin p`, and reconstruct the
trace inside each visible fiber from the digit stream.
    thm:conclusion-uniaxial-zp-replay-reversibilization -/
theorem paper_conclusion_uniaxial_zp_replay_reversibilization {Ω X S : Type*} [Fintype S]
    [DecidableEq S] (f : Ω → X) (trace : Ω → ℕ → S)
    (hsep : ∀ {ω ω'}, f ω = f ω' → trace ω = trace ω' → ω = ω') :
    ∃ p : ℕ, Nat.Prime p ∧ Fintype.card S < p ∧
      ∃ code : Ω → (ℕ → Fin p),
        Function.Injective (fun ω => (f ω, code ω)) ∧
          (∀ ω ω' N, (∀ n < N, trace ω n = trace ω' n) → ∀ n < N, code ω n = code ω' n) := by
  classical
  obtain ⟨p, hp_gt, hp_prime⟩ := Nat.exists_infinite_primes (Fintype.card S + 1)
  have hcard_lt : Fintype.card S < p := by omega
  let emb : S ↪ Fin p :=
    conclusion_uniaxial_zp_replay_reversibilization_symbolEmbedding (S := S) (le_of_lt hcard_lt)
  refine ⟨p, hp_prime, hcard_lt, ?_⟩
  refine ⟨fun ω n => emb (trace ω n), ?_, ?_⟩
  · intro ω ω' hpair
    have hf : f ω = f ω' := congrArg Prod.fst hpair
    have hcode : (fun n => emb (trace ω n)) = fun n => emb (trace ω' n) := congrArg Prod.snd hpair
    have htrace : trace ω = trace ω' := by
      funext n
      exact emb.injective (congrFun hcode n)
    exact hsep hf htrace
  · intro ω ω' N hprefix n hn
    exact congrArg emb (hprefix n hn)

end Omega.Conclusion
