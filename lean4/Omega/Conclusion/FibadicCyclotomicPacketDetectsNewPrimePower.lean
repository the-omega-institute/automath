import Mathlib

/-- Paper label: `cor:conclusion-fibadic-cyclotomic-packet-detects-new-prime-power`. -/
theorem paper_conclusion_fibadic_cyclotomic_packet_detects_new_prime_power
    (Pi : ℕ → ℕ) (z : ℕ → ℕ → ℕ) (hpos : ∀ d, 0 < Pi d)
    (hcontent :
      ∀ d p, 2 ≤ d → Nat.Prime p → (p ∣ Pi d ↔ ∃ k, 1 ≤ k ∧ z p k = d))
    (d : ℕ) (hd : 2 ≤ d) :
    1 < Pi d ↔ ∃ p k, Nat.Prime p ∧ 1 ≤ k ∧ z p k = d := by
  constructor
  · intro hgt
    obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd (show Pi d ≠ 1 by omega)
    obtain ⟨k, hk, hzk⟩ := (hcontent d p hd hpprime).mp hpdvd
    exact ⟨p, k, hpprime, hk, hzk⟩
  · rintro ⟨p, k, hpprime, hk, hzk⟩
    have hpdvd : p ∣ Pi d := (hcontent d p hd hpprime).mpr ⟨k, hk, hzk⟩
    exact lt_of_lt_of_le hpprime.one_lt (Nat.le_of_dvd (hpos d) hpdvd)
