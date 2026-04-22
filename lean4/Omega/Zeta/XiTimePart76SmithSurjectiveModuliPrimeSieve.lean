import Mathlib.Data.Nat.Totient
import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part76-smith-surjective-moduli-prime-sieve`. -/
theorem paper_xi_time_part76_smith_surjective_moduli_prime_sieve
    (dTop q r : ℕ) (hd : 0 < dTop) (hr : r < dTop) :
    (∀ b : ℕ, Nat.Coprime dTop b ↔ Nat.gcd dTop b = 1) ∧
      (((Finset.range (q * dTop + r)).filter fun b => Nat.Coprime dTop b).card =
        q * Nat.totient dTop + ((Finset.range r).filter fun b => Nat.Coprime dTop b).card) := by
  let p : ℕ → Prop := Nat.Coprime dTop
  have _ := hd
  have _ := hr
  refine ⟨fun _ => Iff.rfl, ?_⟩
  have hperiod : Function.Periodic p dTop := Nat.periodic_coprime dTop
  have hcount_mul : Nat.count p (q * dTop) = q * Nat.count p dTop := by
    induction q with
    | zero =>
        simp
    | succ q ih =>
        have hshift : Nat.count (fun b => p (q * dTop + b)) dTop = Nat.count p dTop := by
          congr 1
          funext b
          simpa [add_comm] using (hperiod.nat_mul q b)
        rw [Nat.succ_mul, Nat.count_add, ih, hshift, Nat.succ_mul]
  have hcount_add : Nat.count p (q * dTop + r) = q * Nat.count p dTop + Nat.count p r := by
    have hshift : Nat.count (fun b => p (q * dTop + b)) r = Nat.count p r := by
      congr 1
      funext b
      simpa [add_comm] using (hperiod.nat_mul q b)
    rw [Nat.count_add, hcount_mul, hshift]
  have htotient : Nat.count p dTop = Nat.totient dTop := by
    exact (Nat.count_eq_card_filter_range p dTop).trans <| by
      simpa [p] using (Nat.totient_eq_card_coprime dTop).symm
  calc
    ((Finset.range (q * dTop + r)).filter fun b => Nat.Coprime dTop b).card
        = Nat.count p (q * dTop + r) := by
          simpa [p] using (Nat.count_eq_card_filter_range p (q * dTop + r)).symm
    _ = q * Nat.count p dTop + Nat.count p r := hcount_add
    _ = q * Nat.totient dTop + ((Finset.range r).filter fun b => Nat.Coprime dTop b).card := by
          simp [htotient, p, Nat.count_eq_card_filter_range]

end Omega.Zeta
