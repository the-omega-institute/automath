import Mathlib.Tactic

namespace Omega.Zeta

/-- Paper label: `thm:xi-replica-softcore-exceptional-inertia-index-rigidity-floor`. -/
theorem paper_xi_replica_softcore_exceptional_inertia_index_rigidity_floor
    (neg : Nat -> Nat)
    (hRankOne : ∀ q, 1 ≤ q ->
      neg q = (q + 1) / 2 ∨ neg q + 1 = (q + 1) / 2)
    (hParity : ∀ q, 1 ≤ q -> neg q % 2 = ((q * (q + 1) / 2) % 2)) :
    ∀ q, 1 ≤ q -> neg q = (q + 1) / 2 := by
  intro q hq
  cases hRankOne q hq with
  | inl h => exact h
  | inr h =>
      have hOdd :
          Odd (q * (q + 1) / 2) ↔ Odd ((q + 1) / 2) := by
        obtain ⟨r, hq | hq⟩ := Nat.even_or_odd' q
        · subst q
          have hleft : (2 * r * (2 * r + 1) / 2) = r * (2 * r + 1) := by
            rw [Nat.mul_assoc, Nat.mul_div_right _ (by decide : 0 < 2)]
          have hright : (2 * r + 1) / 2 = r := by omega
          rw [hleft, hright, Nat.odd_mul]
          simp
        · subst q
          have hsucc : 2 * r + 1 + 1 = 2 * (r + 1) := by omega
          have hleft :
              ((2 * r + 1) * (2 * r + 1 + 1) / 2) =
                (2 * r + 1) * (r + 1) := by
            rw [hsucc, Nat.mul_comm, Nat.mul_assoc,
              Nat.mul_div_right _ (by decide : 0 < 2), Nat.mul_comm]
          have hright : (2 * r + 1 + 1) / 2 = r + 1 := by omega
          rw [hleft, hright, Nat.odd_mul]
          simp
      have htri : (q * (q + 1) / 2) % 2 = ((q + 1) / 2) % 2 := by
        by_cases hqOdd : Odd (q * (q + 1) / 2)
        · rw [Nat.odd_iff.mp hqOdd, Nat.odd_iff.mp (hOdd.mp hqOdd)]
        · rw [Nat.not_odd_iff.mp hqOdd, Nat.not_odd_iff.mp (fun h => hqOdd (hOdd.mpr h))]
      have hpar : neg q % 2 = ((q + 1) / 2) % 2 := by
        rw [hParity q hq, htri]
      have hpos : 1 ≤ (q + 1) / 2 := by omega
      omega

end Omega.Zeta
