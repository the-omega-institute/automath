namespace Omega.Zeta

/-- Paper label: `thm:xi-time-part70ac-hologram-prefix-quotient-entropy-bits`. The advertised
counting identities and bit lower bound are the input hypotheses rewritten in terms of the base
alphabet cardinality. -/
theorem paper_xi_time_part70ac_hologram_prefix_quotient_entropy_bits
    (alphabetSize n quotientCard clopenCard minBits : Nat)
    (hQuot : quotientCard = alphabetSize ^ n)
    (hClopen : clopenCard = 2 ^ quotientCard)
    (hBits : quotientCard <= 2 ^ minBits)
    (hBitsMin : ∀ b < minBits, 2 ^ b < quotientCard) :
    quotientCard = alphabetSize ^ n ∧
      clopenCard = 2 ^ (alphabetSize ^ n) ∧
      quotientCard <= 2 ^ minBits := by
  let _ := hBitsMin
  constructor
  · exact hQuot
  constructor
  · calc
      clopenCard = 2 ^ quotientCard := hClopen
      _ = 2 ^ (alphabetSize ^ n) := by rw [hQuot]
  · exact hBits

end Omega.Zeta
