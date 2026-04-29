import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Prod

namespace Omega.Conclusion

theorem paper_conclusion_rhsharp_q_amplified_address_barrier {P R : Type*} [Fintype P]
    [Fintype R] (b n : ℕ) (hb : 0 < b) (addr : P → Fin b) (reg : P → R)
    (hbig : n ≤ Fintype.card P) (hinj : Function.Injective fun p => (addr p, reg p)) :
    n / b ≤ Fintype.card R := by
  have hcard :
      Fintype.card P ≤ b * Fintype.card R := by
    simpa [Fintype.card_fin, Fintype.card_prod] using
      Fintype.card_le_of_injective (fun p => (addr p, reg p)) hinj
  have hdiv := Nat.div_le_div_right (c := b) (le_trans hbig hcard)
  simpa [Nat.mul_comm, Nat.mul_div_right _ hb] using hdiv

end Omega.Conclusion
